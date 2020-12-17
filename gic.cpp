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
		if (sat_solve (init_->s(), bad_))  
			return true;
		Cube uc = get_uc ();
		initialize_invariant (uc);  
					
		while (!invariant_check ()){ //  C /\ T /\ \neg C'
		    
		    State* t = get_new_state (); //get assignment in \neg C'
		    if (sat_solve (t->s(), bad_)){
		    	solver_->update_state_input (t->input());
		    	Assignment partial_t = get_partial (t); 
		    	update_bad (partial_t);      
		    	if (sat_solve (init_->s(), bad_))
		    		return true;
		    	uc = get_uc ();
		    	renew_invariant (uc); //two different implementations
		    }
		    else{
		    	uc = get_uc ();
		    	update_invariant (uc); 
		    }
		}
		return false;
	}
	
	// bool Gic::backward_gic_check (){
	// 	if (sat_solve (init_flag_, bad_))  
	// 		return true;
	// 	initialize_invariant (get_uc ());  
					
	// 	while (!invariant_check ()){ //  /neg C /\ T /\ C'
		    
	// 	    State* t = get_new_state (); //get assignment in /neg C
	// 	    if (sat_solve (init_flag_, t)){
	// 	    	Assignment& partial_t = get_partial (t); 
	// 	    	update_init (partial_t);     
	// 	    	if (sat_solve (init_flag_, bad_))
	// 	    		return true;
	// 	    	renew_invariant (bad_); //two different implementations
	// 	    }
	// 	    else
	// 	    	update_invariant (get_uc ())  
	// 	}
	// 	return false;
	// }
	
	
	
	/***********************help function****************************/
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
		init_flag_ = 0;
	}


	void Gic::gic_initialization (){
		solver_ = new MainSolver (model_, stats_,verbose_);
		inv_solver_ = new InvSolver (model_, verbose_);
		
		// if(!forward_){
		// 	init_flag_ = solver->get_flag();
		// 	Clause& tmp;
		// 	tmp.push_back (init_flag_);
		// 	for (auto it = init_->s().begin();it != init_->s().end();it++){
		// 		tmp.push_back (-(*st));
		// 		solver_->add_clause (-init_flag_, *it);
		// 	}
		// 	solver_->add_clause (tmp);
		// 	//initialize init_ to a new_flag and add equivlance 
		// }
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
	}

	bool Gic::immediate_satisfiable ()
	{
	    bool res = sat_solve (init_->s (), bad_);
	    /*if (res)
	    {
	        Assignment st = solver_->get_model ();
	        std::pair<Assignment, Assignment> pa = state_pair (st);
	        if (forward_)
	            init_->set_inputs (pa.first);
	        else
	            last_ = new State (NULL, pa.first, pa.second, forward_, true);
	        
	        return true;
	    }*/

	    return res;
	}
	
	bool Gic::sat_solve (Assignment& s, int bad) {
		Cube assumption = s;
		if (abs(bad)*2 <= model_->max_id ()) //it is not a flag bad
			assumption.push_back (model_->prime (bad)); 
		else
			assumption.push_back (bad);
		
		stats_->count_main_solver_SAT_time_start ();
	    bool res = solver_->solve_with_assumption (assumption);
	    stats_->count_main_solver_SAT_time_end ();
	    return res;
	}

	bool Gic::sat_solve (State* start, State* next){
		Cube assumption = start->s();
		Cube& s = next->s();
		for (int i = 0; i < s.size (); ++i){
			assumption.push_back (model_->prime (s[i]));
		}
		stats_->count_main_solver_SAT_time_start ();
	    bool res = solver_->solve_with_assumption (assumption); //to be done
	    stats_->count_main_solver_SAT_time_end ();
	    return res;
	}	
	
	bool Gic::sat_solve (int init_flag, State* next){
		Cube assumption;
		assumption.push_back(init_flag);
		Cube& s = next->s();
		for (int i = 0; i < s.size (); ++i){
			assumption.push_back (model_->prime (s[i]));
		}
		stats_->count_main_solver_SAT_time_start ();
	    bool res = solver_->solve_with_assumption (assumption); //to be done
	    stats_->count_main_solver_SAT_time_end ();
	    return res;
	}

	Cube Gic::get_uc () {
		Cube uc = solver_->get_uc ();
		int id = forward_ ? bad_ : init_flag_;
		for (auto it = uc.begin(); it != uc.end(); ++it){
			if (id == *it){
				uc.erase (it);
				break;
			}
		}
		assert (!uc.empty ());
		return uc;
	}
	
	void Gic::initialize_invariant (Cube& uc) {
		assert (inv_.size () == 0);
		if (forward_){
			assert (inv_solver_ != NULL);
			inv_push (uc);
		}
		// else{
		// 	//inv_push (bad_);/*do not push bad_ to inv_, it is by default that bad_ is in inv_ for backward*/
		// }
	}
	
	bool Gic::invariant_check(){
		assert (inv_solver_ != NULL);
		
		if (forward_){
			for (auto it = inv_.begin(); it != inv_.end(); ++it){
				if (inv_solver_->solve_with_assumption (*it))
					return false;  //add flag assumption
			}
			return true;
		}
		// else{
		// /*
		// 	for (auto it = inv_.begin(); it != inv_.end()); ++it){
		// 		if (inv_solver_->solve_with_assumption (inv_prime (*it))) //to be done
		// 			return false;
		// 	}
		// 	return true;
		// 	*/
		// }
		return false;
	}
	
	Assignment Gic::inv_prime (Assignment& cu){
		Assignment res;
		auto it = cu.begin();
		it ++;
		for (; it != cu.end(); ++it)
			res.push_back (model_->prime (*it));
		return res;
	} 


	void Gic::renew_invariant (Cube& uc){
		if (forward_){
			invsolver_add_flag_assumption ();   
			inv_.clear();
			assert (inv_solver_ != NULL);
			inv_push (uc);
			
		}
		// else{
		// /*
		// 	invsolver_add_flag_assumption ();
		// 	Cube temp;
		// 	temp = inv_[0];
		// 	inv_.clear ();
		// 	inv_.push_back(temp);
		// 	*/
		// }
		//MORE efficient algorithm is NEEDED!
	}
	/*add flag assumption to decide which clause works*/
	void Gic::invsolver_add_flag_assumption (){
		if(forward_){
			for (auto it = inv_.begin();it != inv_.end();it++)
				inv_solver_->flag_assumption_push_back(-(*it)[0]);
		}
		// else{
		// 	auto it = inv_.begin();
		// 	it++;
		// 	for (;it != inv_.end();it++){
		// 		inv_solver_.flag_assumption.push_back(-(*it)[0]);
		// 	}
		// }
	}


	void Gic::update_invariant (Cube& uc){
		assert (inv_solver_ != NULL);
		inv_push (uc);
	}
	
	void Gic::update_bad (Assignment& t) {
		bads_.push_back (t);
		add_bad_to_solver (t); 
	}
	
	void Gic::inv_push(Cube uc){
		uc.insert (uc.begin(), inv_solver_->get_flag ());
		inv_.push_back(uc);
		Clause temp;
		temp.push_back(-uc[0]);
		auto it = uc.begin();
		it++;
		if (forward_){
			for (;it != uc.end();it++)
				temp.push_back (model_->prime(-(*it)));//forward
		}
		// else{
		// 	for (;it != uc.end();it++)
		// 		temp.push_back (-(*it));//backward
		// }
		inv_solver_->add_clause(temp);     //add !uc as clause to solver
	}

	void Gic::inv_push(int bad){
		Clause temp;
		temp.push_back(-inv_solver_->get_flag ());
		temp.push_back(-bad);     //?unsure
		inv_solver_->add_clause(temp);     //add !uc as clause to solver
	}


	void Gic::add_bad_to_solver (Cube& st){
		int flag = solver_->get_flag ();
		int new_bad = solver_->get_flag ();
		solver_->add_equivalence (-new_bad, model_->prime (-bad_), -flag); //bad is in the prime version!!
		Clause tmp;
		tmp.push_back (flag);
		for (auto it = st.begin (); it != st.end(); ++it){
			tmp.push_back (-(*it));
			solver_->add_clause (-flag, *it);
		}
		solver_->add_clause (tmp);
	}
	
	void Gic::update_init (State* t) {
		inits_.push_back (t);
		add_init_to_solver (t->s()); 
	}
	
	void Gic::add_init_to_solver (Cube& st){
		int flag = solver_->get_flag ();
		int new_init = solver_->get_flag ();
		init_flag_ = new_init;
		
		solver_->add_equivalence (-new_init, -init_flag_, -flag);
		Clause tmp;
		tmp.push_back (flag);
		for (auto it = st.begin (); it != st.end(); ++it){
			tmp.push_back (-(*it));
			solver_->add_clause (-flag, *it);
		}
		solver_->add_clause (tmp);
	}

	State* Gic::get_new_state (){
		Assignment st = inv_solver_->get_state (forward_); //to be done
		std::pair<Assignment, Assignment> pa = state_pair (st);
		State* res = new State (pa.first, pa.second, forward_);
		
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
	
	Assignment Gic::get_partial (State* t){//more than one implementation
		if (forward_){
			Assignment tmp = t->s ();
			tmp.insert (tmp.begin(), t->input().begin(), t->input().end());
			assert (!sat_solve (tmp, -bad_));
		}
		// else{
		// 	return t->s ();
		// }	
		return get_uc (); //pay attention to that if an input var is in the returned UC
	}
	
}	
