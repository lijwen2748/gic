#include "gic.h"
#include <vector>
#include <iostream>
#include "utility.h"
#include "statistics.h"
using namespace std;


namespace gic{

	bool Gic::check (std::ofstream& out){
		if (model_->num_outputs () == 0) {
			cout << "Warning: No property (output) needs to be verified" << endl;
			return false; 
		}
		else if (model_->num_outputs () > 1) {
			cout << "Warning: the number of outputs is more than 1, will only take the first one as the property to verify .." << endl;
		}
		
		bad_ = model_->output (0);
	        
	    //for the particular case when bad_ is true or false
	    if (bad_ == model_->true_id ()){
	    	out << "1" << endl;
	        out << "b0" << endl;
	        if (evidence_){
	        //print init state
	        	out << init_->latches() << endl;
	        	//print an arbitary input vector
	        	for (int j = 0; j < model_->num_inputs (); j ++)
	        		out << "0";
	        	out << endl;
	        }
	        out << "." << endl;
	        if (verbose_){
	        	cout << "return SAT since the output is true" << endl;
	        }
	        return true;
	    }
	    else if (bad_ == model_->false_id ()){
	        out << "0" << endl;
	        out << "b" << endl;
	        out << "." << endl;
	        if (verbose_){
	        	cout << "return UNSAT since the output is false" << endl;
	        }
	        return false;
	    }
	        
	    gic_initialization ();
	    bool res = gic_check ();
	    if (res)
    		out << "1" << endl;
   	    else
    		out << "0" << endl;
    	    out << "b0"<< endl;
   	    
            if (evidence_ && res)
    		print_evidence (out);

    	    out << "." << endl;
	    gic_finalization ();
	    return res;
	}	
	

	bool Gic::gic_check (){
		if (verbose_)
			cout << "start check ..." << endl;
		if (immediate_satisfiable ()){
			if (verbose_)
				cout << "return SAT from immediate_satisfiable" << endl;
			return true;
		}
		
		if (forward_) 
			return false;//forward_gic_check ();
		else 
		 	return backward_gic_check ();
	}
	
	bool Gic::backward_gic_check (){
		if (sat_solve (init_->s(), bad_))
			return true;
		while (inv_sat_solve (-bad_, bad_)){
			Cube block_intersect;
			State *s = get_state ();
			states_.push_back (s);
			if (deep_check (s))
				return true;
			//cout << "common_ is " << endl;
			//gic::print (common_);
			common_.clear ();
			states_.pop_back ();
			delete s;
		}
		return false;
	}
	
	bool Gic::deep_check (State* t){
		if (sat_solve (init_, t))
			return true;
		inv_solver_->add_clause_from_cube (t->s());
		if (common_.empty ())
			set_common (t->s());
			
		LOOP_START:
		while (inv_common_sat_solve (-bad_, t)){
			State* s = get_state ();
			update_common_with (s);
			if (common_.empty () || common_in_initial ()){
				set_common (s->s ());
			}
			
			states_.push_back (s);
			if (deep_check (s))
				return true;
			states_.pop_back ();
			delete s;
			
			if (is_blocked(t))
				return false;
			else{
				set_common (t->s());
			}
		}
		Cube mic = get_mic (inv_solver_);
		std::sort (mic.begin(), mic.end(), gic::comp);
		if (gic::imply (common_, mic)){
			inv_solver_->add_clause_from_cube (mic);
			set_common (mic);
			return false;
		}
		else{
			set_common (mic);
			goto LOOP_START;
		}
		
		return false;
	}
	
	void Gic::set_common (Cube& st){
		common_ = st;
		common_flag_ = inv_solver_->get_flag ();
	}
	
	bool Gic::is_blocked (State* t){
		return gic::imply (t->s(), common_);
	}
	
	bool Gic::common_in_initial (){
		return gic::imply (init_->s(), common_);
	}
	
	void Gic::update_common_with (State* s){
		Cube& st = s->s();
		int start = model_->num_inputs() + 1;
		Cube tmp;
		for (auto it = common_.begin(); it != common_.end (); ++it){
			if (st[abs(*it)-start] == (*it))
				tmp.push_back (*it);
		}
		common_ = tmp;
	}
	
	bool Gic::inv_common_sat_solve (int not_bad, State* t){
		Cube cl = common_;
		cl.push_back (common_flag_);
		inv_solver_->add_clause_from_cube (cl);
		
		Cube assumption = t->s();
		assumption.insert (assumption.begin(), common_.begin(), common_.end());
		for (int i  = 0; i < assumption.size (); ++i)
			assumption[i] = model_->prime (assumption[i]);
		assumption.push_back (common_flag_);
		assumption.push_back (-bad_);
		stats_->count_main_solver_SAT_time_start ();
		//inv_solver_->print_clauses ();
	    bool res = inv_solver_->solve_with_assumption (assumption);
	    stats_->count_main_solver_SAT_time_end ();
	    if (res){//set the evidence
	    
	    }
	    return res;
	}
	
	/*
	bool Gic::backward_gic_check (){
		if (sat_solve (init_->s(), bad_))
			return true;
		while (inv_sat_solve (-bad_, bad_)){
			Cube block_intersect;
			State *s = get_state ();
			states_.push_back (s);
			if (deep_check (s,block_intersect))
				return true;
		}
		return false;
	}
	
	bool Gic::deep_check (State* t, Cube& block_intersect){
		if (sat_solve (init_, t))
			return true;
		inv_solver_->add_clause_from_cube (t->s());
		//gic::print (t->s());
		while (inv_sat_solve (-bad_, t)){
			State *s = get_state ();
			Cube temp_s = s->s();
			Cube intersection;
			intersect (temp_s,t->s(),intersection);
			if (intersection.empty())
				intersection = s->s();
			if (in_initial (intersection))
				intersection = s->s();
			
			states_.push_back (s);
			if (deep_check (intersection,temp_s,block_intersect))
				return true;
		}
		Cube mic = get_mic (inv_solver_);
		inv_solver_->add_clause_from_cube (mic);
		//cout << "block mic " << mic.size() << endl;
		//gic::print (mic);
		return false;
	}

	bool Gic::deep_check (Cube &intersect_uc, Cube t, Cube& block_intersect){
		if (sat_solve (init_, t))
			return true;
		//inv_solver_->add_clause_from_cube (t->s());
		//gic::print (t->s());
		while (inv_sat_solve (intersect_uc, t)){
			State *s = get_state ();
			Cube temp_s = s->s();
			Cube intersection = intersect_uc;
			intersect (temp_s,t,intersection);
			if (intersection.empty())
				intersection = s->s();
			if (in_initial (intersection))
				intersection = s->s();
			
			states_.push_back (s);
			if (deep_check (intersection,temp_s, block_intersect))
				return true;
			std::sort (t.begin(), t.end(), gic::comp);
			if (gic::imply (t,block_intersect)){
				//cout<<"block works"<<endl;
				return false;
			}
				
			
		}
		//cout<<"try"<<endl;
		Cube mic = get_mic (inv_solver_);
		std::sort (mic.begin(), mic.end(), gic::comp);
		std::sort (intersect_uc.begin(), intersect_uc.end(), gic::comp);
		if (gic::imply (intersect_uc, mic)){
			//cout<<"return block"<<endl;
			block_intersect = mic;
			inv_solver_->add_clause_from_cube (mic);
			return false;
		}
		else{
			block_intersect = t;
			return deep_check (t,t,block_intersect);
		}
			
		//cout << "block mic " << mic.size() << endl;
		//gic::print (mic);
		
	}



	void Gic::intersect (Cube& main_state, Cube& t, Cube& intersection){
		Cube tail;
		Cube perfix;
		if (intersection.empty()) intersection = t;
	    for (auto it = intersection.begin(); it != intersection.end(); ++it) {
	    	if (main_state[abs(*it)-model_->num_inputs ()-1] == *it) 
	    		perfix.push_back (*it);
		else 
			tail.push_back (*it);
	    }
		tail.insert (tail.begin (),perfix.begin (),perfix.end());
		main_state = tail;
		intersection = perfix;

	}
	bool Gic::in_initial (Cube &cu){
		for (auto it = cu.begin();it != cu.end();++it)
			if (*it > 0) return false;
		return true;
	}

	bool Gic::try_reduce (Cube s, Cube t){
		int start_id = model_->num_inputs()+1;
		while (true){
			Cube cu;
			for (auto it = t.begin(); it != t.end(); ++it){
				if (s[abs(*it)-start_id] == (*it))
					cu.push_back (*it);
			}
			if (cu.empty ())
				return false;
			if (gic::imply (init_->s(), cu))
				return false;
			Cube tmp = cu;
			tmp.push_back (inv_solver_->get_flag());
			inv_solver_->add_clause_from_cube (tmp);
			for (int i = 0; i < tmp.size()-1; ++i)
				tmp[i] = model_->prime (tmp[i]);
			bool res = inv_solver_->solve_with_assumption (tmp);
			if (!res){
				//cout << "block state " << cu.size() << endl;
				//gic::print (cu);
				return true;
			}
			State *st = get_state ();
			s = st->s();
			t = cu;
				
		}
		return false;
	}
	*/
	
	Cube Gic::get_mic (SATSolver* solver){
		Cube uc = get_uc (solver);
		/*
		cout << "before reduce " << uc.size() << endl;
		gic::print (uc);
		int max_fail = 3;
		int count_fail = 0;
		for (int i = 0; i < uc.size(); ++i){
			if (inv_sat_solve (uc, i)){
				++count_fail;
				if (count_fail >= max_fail)
					break;
			}
			else{
				uc = get_uc (solver);
				i = -1;
			}
			
		}
			
		cout << "after reduce " << uc.size() << endl;
		gic::print (uc);
		*/
		return uc;
	}
	
	bool Gic::inv_sat_solve (Cube& cu, int n){
		Cube tmp;
		for (int i = 0; i < cu.size(); ++i){
			if (i != n){
				tmp.push_back (cu[i]);
			}
		}
		tmp.push_back (inv_solver_->get_flag ());
		inv_solver_->add_clause_from_cube (tmp);
		
		Cube assumption;
		for (int i = 0; i < tmp.size()-1; ++i){
			assumption.push_back (model_->prime (tmp[i]));
		}
		assumption.push_back (tmp.back ());
		
		stats_->count_main_solver_SAT_time_start ();
		//inv_solver_->print_clauses ();
	    bool res = inv_solver_->solve_with_assumption (assumption);
	    stats_->count_main_solver_SAT_time_end ();
	    if (res){//set the evidence
	    
	    }
	    return res;
	}

	bool Gic::inv_sat_solve (Cube& cu, Cube& t){
		Cube assumption;
		Cube cl;
		cl.insert(cl.begin(),cu.begin(),cu.end());
		int length = t.size();
		if (cu.size() == length)
			inv_solver_->add_clause_from_cube (t);
		else
		{
			int flag = inv_solver_->get_flag();
			cl.push_back (flag);
			inv_solver_->add_clause_from_cube (cl);
			assumption.push_back (flag);
		}
		
		for (auto it = t.begin (); it != t.end (); ++it)
			assumption.push_back (model_->prime (*it));
		assumption.push_back (-bad_);
		
		stats_->count_main_solver_SAT_time_start ();
	    bool res = inv_solver_->solve_with_assumption (assumption);
	    stats_->count_main_solver_SAT_time_end ();
	    if (res){//set the evidence
	    
	    }
	    return res;
	}
	
	
	/*
	void Gic::set_partial (State* s){
		bool res = inv_sat_solve (s);
		if (!res){
			//cout << "get partial state success" << endl;
			Cube cu = get_uc (inv_solver_);
			remove_input (cu);
			s->set_partial (cu);
		}
	}
	*/
	
	
	/*========================helper function==================*/
	Gic::Gic (Model* model, Statistics& stats, std::ofstream* dot, bool forward, bool evidence, bool verbose){
		model_ = model;
		stats_ = &stats;
		dot_ = dot;
		solver_ = NULL;
		inv_solver_ = NULL;
		init_ = new State (model_->init ());
		forward_ = forward;
		evidence_ = evidence;
		verbose_ = verbose;
	}
	
	void Gic::gic_initialization (){
		solver_ = new MainSolver (model_, stats_,verbose_);
		inv_solver_ = new InvSolver (model_, verbose_);
		
		if (forward_){
		//add !bad' as the constraint
			Cube cu;
			cu.push_back (bad_);
			inv_solver_add_clause_from_cube (cu);
		}
		
		last_ = new State ();
		
	}
	
	void Gic::gic_finalization (){
		if (solver_ != NULL) {
	        delete solver_;
	        solver_ = NULL;
	    }
	    if (inv_solver_ != NULL) {
	        delete inv_solver_;
	        inv_solver_ = NULL;
	    }
	    for(auto it = states_.begin(); it != states_.end(); ++it){
	    	if ((*it) != NULL){
	    		delete *it;
	    		(*it) = NULL;
	    	}
	    }
	    if (init_ != NULL){
	    	delete init_;
	    	init_ = NULL;
	    }
	    if (last_ != NULL){
	    	delete last_;
	    	last_ = NULL;
	    }
	}
	
	bool Gic::immediate_satisfiable ()
	{
		Assignment ass = init_->s();
		ass.push_back (bad_);
	    bool res = sat_solve (ass);
	    /*
	    if (res)
	    {
	        Assignment st = solver_->get_model ();
	        std::pair<Assignment, Assignment> pa = state_pair (st);
	        if (forward_)
	            init_->set_inputs (pa.first);
	        else
	            last_ = new State (NULL, pa.first, pa.second, forward_, true);
	        
	        return true;
	    }
	    */

	    return res;
	}
	
	bool Gic::sat_solve (Assignment& st, int bad) {
		Cube assumption = st;
		assumption.push_back (model_->prime (bad));
		
		stats_->count_main_solver_SAT_time_start ();
	    bool res = solver_->solve_with_assumption (assumption);
	    stats_->count_main_solver_SAT_time_end ();
	    if (res){//set the evidence
	    
	    }
	    return res;
	}
	
	bool Gic::inv_sat_solve (int not_bad, int bad) {
		Cube assumption;
		assumption.push_back (not_bad);
		assumption.push_back (model_->prime (bad));
		
		stats_->count_main_solver_SAT_time_start ();
		//inv_solver_->print_clauses ();
	    bool res = inv_solver_->solve_with_assumption (assumption);
	    stats_->count_main_solver_SAT_time_end ();
	    if (res){//set the evidence
	    
	    }
	    return res;
	}
	
	bool Gic::inv_sat_solve (int not_bad, State* t) {
		Cube assumption;
		Cube& st = t->s();
		for (auto it = st.begin (); it != st.end (); ++it)
			assumption.push_back (model_->prime (*it));
		assumption.push_back (not_bad);
		
		stats_->count_main_solver_SAT_time_start ();
	    bool res = inv_solver_->solve_with_assumption (assumption);
	    stats_->count_main_solver_SAT_time_end ();
	    if (res){//set the evidence
	    
	    }
	    return res;
	}

	bool Gic::sat_solve (State* start, State* next){
		Cube assumption = start->s();
		Cube& s = next->partial().empty() ? next->s() : next->partial();
		for (int i = 0; i < s.size (); ++i){
			assumption.push_back (model_->prime (s[i]));
		}
		stats_->count_main_solver_SAT_time_start ();
	    bool res = solver_->solve_with_assumption (assumption); 
	    stats_->count_main_solver_SAT_time_end ();
	    return res;
	}	

	bool Gic::sat_solve (State* start, Cube& next){
		Cube assumption = start->s();
		for (int i = 0; i < next.size (); ++i){
			assumption.push_back (model_->prime (next[i]));
		}
		stats_->count_main_solver_SAT_time_start ();
	    bool res = solver_->solve_with_assumption (assumption); 
	    stats_->count_main_solver_SAT_time_end ();
	    return res;
	}


	/*
	bool Gic::inv_sat_solve (Assignment& st, int level){
		Cube assumption = st;
		assert (level+1 <= invariants_.size());
		for (int i = 0; i < level; ++i){
			assumption.push_back (-invariants_[i].level_flag());
		}
		assumption.push_back (invariants_[level].level_flag ());
		//gic::print (assumption);
		//inv_solver_->print_clauses ();
		return inv_solver_->solve_with_assumption (assumption);
	}
	
	bool Gic::inv_sat_solve (State* s){
		Cube assumption = s->input();
		assumption.insert (assumption.begin(), s->s().begin(), s->s().end());
		//gic::print (assumption);
		//inv_solver_->print_clauses ();
		return inv_solver_->solve_with_assumption (assumption);
	}
	*/
	
	void Gic::inv_solver_add_clause_from_cube (Cube& uc, int level){
		Clause cl;
		assert (level+1 <= invariants_.size());
		cl.push_back (-invariants_[level].level_flag ());
		for (auto it = uc.begin(); it != uc.end(); ++it)
			cl.push_back (-model_->prime(*it));
		inv_solver_->add_clause (cl);
	}
	
	void Gic::inv_solver_add_clause_from_cube (Cube& s){
		Clause cl;
		for (auto it = s.begin(); it != s.end(); ++it){
			cl.push_back (-model_->prime(*it));
		}
		inv_solver_->add_clause (cl);
		//gic::print (s);
	}
	
	Cube Gic::get_uc (SATSolver* solver) {
		Cube uc = solver->get_uc ();
		Cube tmp;
		int id = model_->max_id ()/2;
		for (auto it = uc.begin(); it != uc.end(); ++it){
			if (forward_){
				if (id >= abs(*it))
					tmp.push_back (*it);
			}
			else{
				if (id < abs(*it) && (abs(*it) <= model_->max_id()))
					tmp.push_back (model_->previous (*it));
			}
		}
		uc = tmp;
		assert (!uc.empty ());
		return uc;
	}
	
	void Gic::mark_transition (State* start, State* next){
		State *nt = (next == NULL) ? last_ : next; //the value of last_ has not been assigned!
		start->set_successor (nt);
		nt->set_predecessor (start);
	}
	
	State* Gic::get_state (){
		Assignment st = inv_solver_->get_state (forward_); //to be done
		//std::pair<Assignment, Assignment> pa = state_pair (st);
		State* res = new State (st, forward_);
		
		return res;
	}
	
	void Gic::remove_input (Cube& uc) {
		Cube tmp;
		for (auto it = uc.begin(); it != uc.end(); ++it){
			if (abs(*it) > model_->num_inputs())
				tmp.push_back (*it);
		}
		uc = tmp;
	}
	
	
	Assignment Gic::get_partial (State* t){//more than one implementation
		if (forward_){
			Assignment tmp = t->s ();
			tmp.insert (tmp.begin(), t->input().begin(), t->input().end());
			//solver_->print_clauses();
			//assert (!sat_solve (tmp, -bad_));
			if (!sat_solve (tmp, -bad_))
				return get_uc(solver_);
			return tmp;
		}
		// else{
		// 	return t->s ();
		// }	
		return t->s();
		//return get_uc (); //pay attention to that if an input var is in the returned UC
	}
	
}	
