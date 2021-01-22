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
		 	return pdr_check ();
	}
	
	bool Gic::pdr_check (){
		if (sat_solve (init_->s(), bad_))
			return true;
		Frame* new_frame = new Frame();
		new_frame->frame.push_back (init_->s());
		F_.push_back (new_frame);
		add_frame_level ();
		set_new_frame ();  
		while (true){
			//blocking stage
			while (inv_sat_solve(frame_level_,-bad_)){  //check whether bad state intersect with current frame
				State* c = get_state ();
				if (!rec_block (c,frame_level_)) return false; //to be done
			}
			//propagation stage
			add_frame_level ();
			for (int i = 0;i<frame_level_;i++){
				for (auto it = F_[i]->frame.begin();it != F_[i]->frame.end();++it){
					if (!inv_sat_solve (*it,i-1))
						F_[i+1]->frame.push_back (*it); 
				}
				if (frame_is_equal (i,i+1)) return true;
			}
			
		}
		return false;
	}

	void Gic::set_new_frame (){
		Frame* new_frame = new Frame();
		new_frame->frame.push_back (init_->s());
		F_.push_back (new_frame);
	}
	
	bool Gic::rec_block (Cube& s,int i){
		if (i == 0) return false;
		while (inv_sat_solve (s,i-1)){
			Cube pre_s = get_predecessor (i-1,s);
			if (!rec_block (pre_s,i-1)) return false;
		}
		Cube mic = get_mic(s,i);
		add_mic_to_frame (mic);   //add neg mic as clause
		return true;
	}


	/*
	bool Gic::deep_check (State* t){
		if (sat_solve (init_, t))
			return true;
		inv_solver_->add_clause_from_cube (t->state());
		
		Cube mic = get_mic (inv_solver_, t);
		if (mic.size() != t->state().size()){//unsuccessful
			inv_solver_->add_clause_from_cube (mic);		
			return false;	
		}
		//if (common_.empty ())
			//set_common (t->s());
			
		//LOOP_START:
		while (inv_sat_solve (-bad_, t)){
			State* s = get_state ();
			
			set_partial (s,t);
			//update_common_with (s);
			//if (common_.empty () || common_in_initial ()){
			//	set_common (s->s ());
			//}
			
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
		mic = get_mic (inv_solver_, t);
		inv_solver_->add_clause_from_cube (mic);
		
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

	*/
	
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
	

	
	Cube Gic::get_mic (SATSolver* solver, State* t){
		//Cube uc = get_uc (solver);
		Cube uc = t->state();
		
		//cout << "before reduce " << uc.size() << endl;
		//gic::print (uc);
		int max_fail = 10;
		bool done = false;
		//cout<<"try mic"<<endl;
		for (int iter = 1; iter <= max_fail; ++iter){
			if (done) {
				//cout<<"mic win"<<endl;
				break;
			}
			done = true;
			for (int i = 0; i < uc.size(); ++i){
				if (!inv_sat_solve (uc, i)){
					uc = get_uc (solver);
					Cube uc_comp = complement (t->state(), uc);
					while (!inv_sat_solve (init_, uc)){
						assert (!uc_comp.empty ());
						uc.push_back (*(uc_comp.begin()));
						uc_comp.erase (uc_comp.begin());
					}
					
					done = false;
					break;
				}
			
			}
		}
			
		//cout << "after reduce " << uc.size() << endl;
		//gic::print (uc);
		
		return uc;
	}
	
	Cube Gic::complement (Cube& cu1, Cube& cu2){
		Cube res;
		hash_set<int> tmp_set;
		for (auto it = cu2.begin(); it != cu2.end (); ++it)
			tmp_set.insert (*it);
		for (auto it = cu1.begin(); it != cu1.end (); ++it){
			if (tmp_set.find (*it) == tmp_set.end ())
				res.push_back (*it);
		}
		return res;
	}
	/*
	bool Gic::inv_sat_solve (Cube& cu, int n){
		Cube tmp;
		for (int i = 0; i < cu.size(); ++i){
			if (i != n){
				tmp.push_back (cu[i]);
			}
		}
		
		if (inv_sat_solve (init_->s(), tmp))//included in init_
			return true;
		
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
	*/
	
	bool Gic::inv_sat_solve (State* init, Cube& t){
		Cube assumption = init->s();
		Cube cu = t;
		cu.push_back (inv_solver_->get_flag ());
		inv_solver_->add_clause_from_cube (cu);
		
		assumption.push_back (cu.back ());
		stats_->count_main_solver_SAT_time_start ();
	    bool res = inv_solver_->solve_with_assumption (assumption);
	    stats_->count_main_solver_SAT_time_end ();
	    if (res){//set the evidence
	    
	    }
	    return res;
	}
	bool Gic::inv_sat_solve (Cube& cu, Cube& t){
		Cube assumption = cu;
		assumption.insert (assumption.begin(), t.begin(), t.end());
		stats_->count_main_solver_SAT_time_start ();
	    bool res = inv_solver_->solve_with_assumption (assumption);
	    stats_->count_main_solver_SAT_time_end ();
	    if (res){//set the evidence
	    
	    }
	    return res;
	/*
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
	*/
	}
	
	
	
	void Gic::set_partial (State* s,State* t){
		bool res = inv_partial_solve (s,t);
		if (!res){
			//cout << "get partial state success" << endl;
			Cube cu = get_forward_uc (inv_solver_);
			remove_input_flag (cu);
			std::sort (cu.begin(), cu.end(), gic::comp);
			s->set_partial (cu);
		}
	}

	bool Gic::inv_partial_solve (State* s,State* t){
		
		Cube cl_t;
		Cube assumption = s->input ();
		int t_flag = inv_solver_->get_flag();
		
		
		Cube& st = t->state();
		for (auto it = st.begin (); it != st.end (); ++it)
			cl_t.push_back (model_->prime (*it));
		cl_t.push_back (t_flag);
		inv_solver_->add_clause_from_cube (cl_t);

		assumption.insert (assumption.begin (),s->state().begin(),s->state().end());
		assumption.push_back(t_flag);
		
		stats_->count_main_solver_SAT_time_start ();
	    bool res = inv_solver_->solve_with_assumption (assumption);
	    stats_->count_main_solver_SAT_time_end ();
	    if (res){//set the evidence
	    
	    }
	    return res;
	}
	
	
	
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
	
	bool Gic::inv_sat_solve (int frame_level, int not_bad) {
		Cube assumption;
		assumption.push_back (not_bad);
		int frame_size = F_[frame_level]->frame.size();
		
		for (int i = 0;i < frame_size;i++){

			int flag = F_[frame_level]->frame[i].back();
			if (increase_flag_.find (flag) == increase_flag_.end()){
				Clause& cl = F_[frame_level]->frame[i];
				inv_solver_->add_clause_from_cube (cl);
			}
			assumption.push_back (flag);
			
		}
		stats_->count_main_solver_SAT_time_start ();
		//inv_solver_->print_clauses ();
	    bool res = inv_solver_->solve_with_assumption (assumption);
	    stats_->count_main_solver_SAT_time_end ();
	    if (res){//set the evidence
	    
	    }
	    return res;
	}

	bool Gic::inv_sat_solve (Cube& s, int pre_level){
		Cube assumption;
		
		int pre_size = F_[pre_level]->frame.size();
		//push frame as clasuse
		for (int i = 0;i < pre_size;i++){
			int flag = F_[pre_level]->frame[i].back();
			if (increase_flag_.find (flag) == increase_flag_.end()){
				Clause& cl = F_[pre_level]->frame[i];
				inv_solver_->add_clause_from_cube (cl);
			}
			assumption.push_back (flag);	
		}
		//push !s as clause
		int flag = inv_solver_->get_flag();
		Clause cl = s;
		cl.push_back (flag);
		inv_solver_->add_clause_from_cube (cl);
		assumption.push_back (flag);

		for (auto it = s.begin (); it != s.end (); ++it)
			assumption.push_back (model_->prime (*it));


		stats_->count_main_solver_SAT_time_start ();
	    bool res = inv_solver_->solve_with_assumption (assumption);
	    stats_->count_main_solver_SAT_time_end ();
	    if (res){//set the evidence
	    
	    }
	    return res;
	}


	bool Gic::inv_sat_solve (int bad){
		Cube assumption;
		assumption.push_back (bad);
		
		stats_->count_main_solver_SAT_time_start ();
		//inv_solver_->print_clauses ();
	    bool res = inv_solver_->solve_with_assumption (assumption);
	    stats_->count_main_solver_SAT_time_end ();
	    if (res){//set the evidence
	    
	    }
	    return res;
	}

	bool Gic::inv_sat_solve (State* s){
		Cube assumption = s->input ();
		Cube& st = s->state();
		assumption.insert (assumption.begin(),st.begin(),st.end());
		assumption.push_back (-bad_);
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
		Cube& st = t->state();
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
	
	Cube Gic::get_forward_uc (SATSolver* solver) {
		Cube uc = solver->get_uc ();
		Cube tmp;
		int id = model_->max_id ()/2;
		for (auto it = uc.begin(); it != uc.end(); ++it){
				if (id >= abs(*it))
					tmp.push_back (*it);
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
		Assignment st = inv_solver_->get_model (); //to be done
		std::pair<Assignment, Assignment> pa = state_pair (st);
		State *res = new State (NULL, pa.first, pa.second, forward_, false);
		
		return res;
	}
	
	std::pair<Assignment, Assignment> Gic::state_pair (const Assignment& st)
	{
	    assert (st.size () >= model_->num_inputs () + model_->num_latches ());
	    Assignment inputs, latches;
	    for (int i = 0; i < model_->num_inputs (); i ++)
	        inputs.push_back (st[i]);
	    for (int i = model_->num_inputs (); i < st.size (); i ++)
	    {
	        if (abs (st[i]) > model_->num_inputs () + model_->num_latches ())
	            break;
	        latches.push_back (st[i]);
	    }
	    return std::pair<Assignment, Assignment> (inputs, latches);
	}

	void Gic::remove_input_flag (Cube& uc) {
		Cube tmp;
		for (auto it = uc.begin(); it != uc.end(); ++it){
			if (model_->latch_var (abs(*it)) )
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
