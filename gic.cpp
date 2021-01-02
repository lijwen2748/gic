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
			return forward_gic_check ();
		// else 
		// 	return backward_gic_check ();
	}
	
	bool Gic::forward_gic_check (){
		State *s = NULL;
		while (!inv_check (bad_, s)){
			assert (s != NULL);
			Cube block_t;
			if (!inv_check (s, 1, block_t)){
				//generate_evidence ();
				return true;
			}
			s = NULL;
		}
		//inv_solver_->print_clauses ();
		return false;
	}
	
	bool Gic::inv_check (int bad, State*& s){
		if (invariants_.empty ()){
			if (sat_solve (init_->s(), bad)){
				mark_transition (init_);
				return false;
			}
			Cube uc = get_uc (solver_);
			Invariant inv;
			inv.set_level_flag (inv_solver_->get_flag());
			inv.push_back (InvariantElement (uc));
			invariants_.push_back (inv);
			inv_solver_add_clause_from_cube (uc, 0);
		}
		
		Invariant& inv = invariants_[0];
			
		for (int i = 0; i < inv.size (); ++i){
			if (!inv[i].has_checked()){
				if (inv_sat_solve (inv[i].cube(), 0)){
					s = get_state ();
					if (sat_solve (s->s(), bad)){
						solver_->update_state_input (s->input ()); //update inputs of s
						set_partial (s);
						mark_transition (s);
						states_.push_back (s);
						if (s->partial().size() != 0)
							inv_solver_add_clause_from_cube (s->partial());
						else
							inv_solver_add_clause_from_cube (s->s());
						return false;
					}
					else{
						Cube uc = get_uc (solver_);
						inv.push_back (InvariantElement (uc));
						inv_solver_add_clause_from_cube (uc, 0);
						-- i;
					}
				}
				else
					inv[i].set_checked (true);
			}	
		}
		return true;
	}
	
	bool Gic::inv_check (State* t, int level, Cube& block_t){
		assert (level >= 1);
		assert (invariants_.size() >= level);
		if (invariants_.size() == level){
			if (sat_solve (init_, t)){
				mark_transition (init_, t);
				return false;
			}
			Cube uc = get_uc (solver_, block_t);
			Invariant inv;
			inv.set_level_flag (inv_solver_->get_flag());
			inv.push_back (InvariantElement (uc));
			invariants_.push_back (inv);
			inv_solver_add_clause_from_cube (uc, level);
		}
		
		Invariant* inv = &invariants_[level];
			
		for (int i = 0; i < inv->size (); ++i){
			if (!(*inv)[i].has_checked()){
				if (inv_sat_solve ((*inv)[i].cube(), level)){
					State* s = get_state ();
					if (sat_solve (s, t)){
						solver_->update_state_input (s->input ()); //update inputs of s
						set_partial (s); 
						mark_transition (s, t);
						states_.push_back (s);
						if (s->partial().size() != 0)
							inv_solver_add_clause_from_cube (s->partial());
						else
							inv_solver_add_clause_from_cube (s->s());
						//gic::print(s->s());
						
						Cube block_t_new;
						if (!inv_check (s, level+1, block_t_new))
							return false;
						else {
						
							assert (!block_t_new.empty ());
							if (included (t, block_t_new)){
								block_t = block_t_new;
								return true;
							}
							
							--i; //re-do again to find new state, if exist
							inv = &invariants_[level];
						}
					}
					else{
						Cube uc = get_uc (solver_, block_t);
						inv->push_back (InvariantElement (uc));
						inv_solver_add_clause_from_cube (uc, level);
						-- i;
					}
				}
				else
					(*inv)[i].set_checked (true);
			}	
		}
		add_invariant_to_solver (inv);
		
		int sz = t->partial ().empty () ? t->s().size() : t->partial ().size ();
		if (block_t.size() > 0 && block_t.size () < sz)
			inv_solver_add_clause_from_cube (block_t);
		
		//inv->print ();
		//pop invariants_[level]
		gic::print (block_t);
		gic::print (t->s());
		invariants_.pop_back ();
		inv = NULL;
		return true;
	}
	
	void Gic::set_partial (State* s){
	
		bool res = inv_sat_solve (s);
		if (!res){
			//cout << "get partial state success" << endl;
			Cube cu = get_uc (inv_solver_);
			remove_input (cu);
			std::sort (cu.begin(), cu.end(), gic::comp);
			s->set_partial (cu);
		}
	
	}
	
	void Gic::add_invariant_to_solver (Invariant* inv){
		Clause cl;
		
		if (inv->size () == 1){
			InvariantElement& ie = (*inv)[0];
			if (ie.size () == 1){
				cl.push_back (ie[0]);
				inv_solver_->add_clause (cl);
				return;
			}
		}
		
		for (int i = 0; i < inv->size(); ++i){
			cl.push_back (inv_solver_->get_flag());
		}
		inv_solver_->add_clause (cl);
		
		for (int i = 0; i < inv->size(); ++i){
			InvariantElement& ie = (*inv)[i];
			for (int j = 0; j < ie.size(); ++j){
				Clause tmp;
				tmp.push_back (-cl[i]);
				tmp.push_back (ie[j]);
				inv_solver_->add_clause (tmp);
			}
		}
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
		
		
		//add !bad' as the constraint
		Cube cu;
		cu.push_back (bad_);
		inv_solver_add_clause_from_cube (cu);
		
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
			if (id >= abs(*it)){
				tmp.push_back (*it);
			}
		}
		uc = tmp;
		assert (!uc.empty ());
		return uc;
	}
	
	Cube Gic::get_uc (SATSolver* solver, Cube &st) {
		Cube uc = solver->get_uc ();
		Cube tmp;
		int id = model_->max_id ()/2;
		for (auto it = uc.begin(); it != uc.end(); ++it){
			if (id >= abs(*it)){
				tmp.push_back (*it);
			}
			else{
				int idx = model_->previous (*it);
				auto it2 = st.begin();
				for (; it2 != st.end(); ++it2){
					if (abs (idx) == abs (*it2))
						break;
					if (abs (idx) < abs (*it2)){
						st.insert (it2, idx);
						break;
					}
				}
				if (it2 == st.end ())
					st.push_back (idx);
			}
		}
		uc = tmp;
		assert (!uc.empty ());
		return uc;
	}
	
	bool Gic::included (State* t, Cube& st){
		Cube& s = t->partial().empty () ? t->s() : t->partial();
		return imply (s, st);
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
