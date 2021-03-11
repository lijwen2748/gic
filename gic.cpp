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
	    //print_frame (); 
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
		new_frame->frame_solver = new InvSolver (model_, verbose_);
		new_frame->frame.push_back (init_->s());
		F_.push_back (new_frame);
		frame_level_ = 0;
		set_new_frame (); 
		
		while (true){
			//blocking stage
			while (inv_sat_solve(frame_level_,bad_)){  //check whether bad state intersect with current frame
				State* c = get_state (frame_level_);
				if (!rec_block (c->s(),frame_level_)) return true; 
			}
			//propagation stage
			set_new_frame (); 
			//cout<<"add new frame"<<endl;
			
			for (int i = 1;i<frame_level_;i++){
				for (auto it = F_[i]->frame.begin();it != F_[i]->frame.end();++it){
					if (!inductive_solve (*it,i)){
						F_[i+1]->frame.push_back (*it); 
						F_[i+1]->frame_solver->add_clause_from_cube (*it);
						it = F_[i]->frame.erase (it);
						if (it == F_[i]->frame.end()) break;
						else --it;
					}
				}
				//test if F[i] is equal to F[i+1]
				if (F_[i]->frame.empty()) return false;
			}
		}
		return false;
	}

	void Gic::set_new_frame (){
		Frame* new_frame = new Frame();
		new_frame->frame_solver = new InvSolver (model_, verbose_);
		F_.push_back (new_frame);
		frame_level_++;
	}
	
	bool Gic::rec_block (Cube& s,int i){
		if (i == 0) return false;
		
		while (inductive_solve (s,i-1)){
			//cout<<"before partial "<<s.size()<<endl;
			Cube pre_s = get_predecessor (s,i-1);
			//cout<<"before partial "<<pre_s.size()<<endl;
			if (!rec_block (pre_s,i-1)) return false;
		}	
		
		//cout<<"get mic"<<endl;
		generalize_mic(s,i);
		add_mic_to_frame (s,i);   //add mic as cube,used as neg clause
		return true;
	}

	void Gic::generalize_mic ( Cube& s,int& frame_level){
		
		int max_fail = 3;
		Cube required;
		int fail = 0;

		for (int i = 0; i < s.size(); ++i){
			Cube cand;
			for (int j = 0;j < s.size(); ++j){
				if (j != i) cand.push_back (s[j]);
			}

			if (down (frame_level-1,cand,required)){
				s = cand;
				fail = 0;
			}
			else{
				if (++fail > max_fail) break;
				required.push_back(s[i]);
			}
		}
	}

	bool Gic::down ( int pre_level,Cube& c, Cube& required){
		while (true){
			if (inv_sat_solve (init_->s(), c)) return false;
			if (!is_sat_assuming (c,pre_level)){
				Cube uc = get_uc(F_[pre_level]->frame_solver);
				Cube uc_comp = complement (c, uc);
				while (!inv_sat_solve (init_, uc)){
				
					assert (!uc_comp.empty());
					uc.push_back (*(uc_comp.begin()));
					uc_comp.erase (uc_comp.begin());
				}
				c = uc;
				return true;
			}
			else{
				Cube s = get_predecessor (c,pre_level);
				Cube uc_comp = complement (c, s);
				if (get_intersection (uc_comp,required).size() != 0) return false;
				c = get_intersection (c,s);
			}
		}
	}
	
	bool Gic::cube_non_neg (Cube& uc){
		for (auto it = uc.begin();it != uc.end();++it){
			if ((*it) > 0) return true;
		}
		return false;
	}

	int Gic::get_pos_elem (Cube& uc){
		for (auto it = uc.begin();it != uc.end();++it){
			if ((*it) > 0) return *it;
		}
	}

	Cube Gic::get_intersection (Cube& a, Cube& b){
		Cube res;
		std::set<int> temp_set;
		for (auto it = b.begin();it != b.end(); ++it)
			temp_set.insert (*it);
		for (auto it = a.begin();it != a.end(); ++it){
			if (temp_set.find(*it) != temp_set.end()){
				res.push_back (*it);
			}
		}
		return res;
	
	}	

	Cube Gic::get_mic (SATSolver* solver, Cube& s,int& frame_level){
		//Cube uc = get_uc (solver);
		Cube uc = s;
		
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
				if (!inv_sat_solve (uc, i ,frame_level)){
					//cout<<"drop "<<uc[i]<<endl;
					uc = get_uc (solver);
					Cube uc_comp = complement (s, uc);
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
	
	bool Gic::is_sat_assuming (Cube& cu,int& frame_level){
		Cube tmp;
		tmp.push_back (F_[frame_level]->frame_solver->get_flag ());
		tmp.insert (tmp.end(),cu.begin(),cu.end());
		F_[frame_level]->frame_solver->add_clause_from_cube (tmp);
		
		Cube assumption;
		for (auto it = cu.begin(); it != cu.end(); ++it){
			assumption.push_back (model_->prime (*it));
		}
		assumption.push_back (tmp.front());
		if (frame_level == 0) assumption.insert (assumption.end(),init_->s().begin(),init_->s().end());
		stats_->count_main_solver_SAT_time_start ();
	    bool res = F_[frame_level]->frame_solver->solve_with_assumption (assumption);
	    stats_->count_main_solver_SAT_time_end ();
	    if (res){//set the evidence
	    
	    }
	    return res;
	}

	bool Gic::inv_sat_solve (State* init, Cube& t){
		Cube assumption = init->s();
		Cube cu = t;
		cu.insert (cu.begin(),inv_solver_->get_flag ());
		inv_solver_->add_clause_from_cube (cu);
		
		assumption.push_back (cu.front ());
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
	}
	
	bool Gic::inv_solve (Cube& cu, Cube& t){ //cu can transit to t
		Cube assumption = cu;
		for (auto it = t.begin(); it != t.end(); ++it)
			assumption.push_back (model_->prime(*it));
		stats_->count_main_solver_SAT_time_start ();
	    bool res = inv_solver_->solve_with_assumption (assumption);
	    stats_->count_main_solver_SAT_time_end ();
	    if (res){//set the evidence
	    
	    }
	    return res;
	}

	bool Gic::initial_solve (Cube& t){
		Cube assumption = init_->s();
		for (auto it = t.begin(); it != t.end(); ++it)
			assumption.push_back (model_->prime(*it));
		
		stats_->count_main_solver_SAT_time_start ();
	    bool res = solver_->solve_with_assumption (assumption);
	    stats_->count_main_solver_SAT_time_end ();
	    if (res){//set the evidence
	    
	    }
	    return res;
	}
	
	
	Cube Gic::get_predecessor (Cube& s,int pre_level){
		State* F_state = get_state(pre_level);
		//assert (inv_solve (F_state->s(),s));
		bool res = inv_partial_solve (F_state,s);
		assert (!res);
		//cout << "get partial state success" << endl;
		Cube cu = get_forward_uc (inv_solver_);
		if (cu.empty()) cu = F_state->s();
		remove_input_flag (cu);
		std::sort (cu.begin(), cu.end(), gic::comp);
		return cu;
	}

	bool Gic::inv_partial_solve (State* F_state,Cube& s){
		
		Cube cl_t;
		Cube assumption = F_state->input ();
		int t_flag = inv_solver_->get_flag();
		cl_t.push_back (t_flag);
		for (auto it = s.begin (); it != s.end (); ++it)
			cl_t.push_back (model_->prime (*it));
		inv_solver_->add_clause_from_cube (cl_t);

		assumption.insert (assumption.begin (),F_state->s().begin(),F_state->s().end());
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

		for (auto it = F_.begin();it != F_.end(); ++it){
			delete (*it)->frame_solver;
			delete *it;   //may cause problem
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
	//used
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
	//used
	bool Gic::inv_sat_solve (int frame_level, int bad) {
		Cube assumption;
		assumption.push_back (model_->prime (bad));
		
		stats_->count_main_solver_SAT_time_start ();
	    bool res = F_[frame_level]->frame_solver->solve_with_assumption (assumption);
	    stats_->count_main_solver_SAT_time_end ();
	    if (res){//set the evidence
	    
	    }
	    return res;
	}
	//used
	bool Gic::inductive_solve (Cube& s, int pre_level){
		Cube assumption;

		//push !s as clause
		int flag = F_[pre_level]->frame_solver->get_flag();
		Clause cl;
		cl.push_back (flag);
		cl.insert (cl.end(),s.begin(),s.end());
		F_[pre_level]->frame_solver->add_clause_from_cube (cl);
		assumption.push_back (flag);

		for (int i = 0; i < s.size(); ++i)
			assumption.push_back (model_->prime (s[i]));
		if (pre_level == 0) assumption.insert (assumption.end(),init_->s().begin(),init_->s().end());
		stats_->count_main_solver_SAT_time_start ();
	    bool res = F_[pre_level]->frame_solver->solve_with_assumption (assumption);
	    stats_->count_main_solver_SAT_time_end ();
	    if (res){//set the evidence
	    
	    }
	    return res;
	}

	
	bool Gic::inv_sat_solve (Cube& cu, int n,int frame_level){
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
		
		int pre_size = F_[frame_level]->frame.size();
		//push frame as clasuse
		for (int i = 0;i < pre_size;i++){
			int flag = F_[frame_level]->frame[i].back();
			if (increase_flag_.find (flag) == increase_flag_.end()){
				increase_flag_.insert (flag);
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

	void Gic::add_mic_to_frame (Cube& mic, int frame_level){
		F_[frame_level]->frame.push_back (mic);
		for (int i = 1;i <= frame_level;i++){
			F_[i]->frame_solver->add_clause_from_cube (mic);
		}
	}
	
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
		//assert (!uc.empty ());
		return uc;
	}
	
	void Gic::mark_transition (State* start, State* next){
		State *nt = (next == NULL) ? last_ : next; //the value of last_ has not been assigned!
		start->set_successor (nt);
		nt->set_predecessor (start);
	}
	
	State* Gic::get_state (int frame_level){
		Assignment st = F_[frame_level]->frame_solver->get_model (); 
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

	void Gic::print_frame (){
		int k = 1;
		auto it = F_.begin();
		++it;
		for (;it != F_.end();++it){
			cout<< "frame "<<k<<endl;
			k++;
			Frame curr = *(*it);
			for (int i = 0;i < curr.frame.size();++i){
				gic::print (curr.frame[i]);
			}
			}
		}

	
}	
