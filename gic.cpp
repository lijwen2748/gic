
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
	        out << "b" << i << endl;
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
    	out << "b" << i << endl;
   		if (evidence_ && res)
    		print_evidence (out);
    	out << "." << endl;
	    gic_finalization ();
	    return res;
	}
	
	void Gic::gic_initialization (){
		
		


		init_flag = solver->get_flag();
		Clause& tmp;
		tmp.push_back (init_flag);
		for (auto it = init_->s().begin();it != init_->s().end();it++){
			tmp.push_back (-(*st));
			solver_->add_clause (-init_flag, *it);
		}
		solver_->add_clause (tmp);
		set_init_flag (init_flag);
		//initialize init_ to a new_flag and add equivlance 
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
		else 
			return backward_gic_check ();
	}
	
	bool Gic::forward_gic_check (){
		if (sat_solve (init_, bad_))  
			return true;
		initialize_invariant (get_uc ());  
					
		while (!invariant_check ()){ //  C /\ T /\ \neg C', to be done
		    
		    State* t = get_new_state (); //get assignment in \neg C', to be done
		    if (sat_solve (t, bad_)){
		    	Assignment& partial_t = get_partial (t); //to be done
		    	update_bad (partial_t);      //to be done
		    	if (sat_solve (init_, bad_))
		    		return true;
		    	renew_invariant (get_uc ()); //two different implementations, to be done
		    }
		    else
		    	update_invariant (get_uc ())  //to be done
		}
		return false;
	}
	
	bool Gic::backward_gic_check (){
		if (sat_solve (init_, bad_))  
			return true;
		initialize_invariant (get_uc ());  
					
		while (!invariant_check ()){ //  /neg C /\ T /\ C', to be done
		    
		    State* t = get_new_state (); //get assignment in /neg C,to be done
		    if (sat_solve (init_, t)){
		    	Assignment& partial_t = get_partial (t); //to be done
		    	update_init (partial_t);      //to be done
		    	if (sat_solve (init_, bad_))
		    		return true;
		    	renew_invariant (bad_); //two different implementations, to be done
		    }
		    else
		    	update_invariant (get_uc ())  //to be done
		}
		return false;
	}
	
	
	
	/***********************help function****************************/
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
	
	Cube& Gic::get_uc () {
		Cube& uc = solver_->get_uc ();
		if (forward_){//remove bad
			for (auto it = uc.begin(); it != uc.end(); ++it)
				if (bad_ == *it){
					uc.erase (it);
					break;
				}
		}
		else{ //remove init
			auto it = init_->s().rbegin ();//the last element of init_
			Cube tmp;
			for (auto iter = uc.begin(); iter != uc.end(); ++iter)
				if (*iter > *it)
					tmp.push_back (*iter);
			uc = tmp;		
		}
		assert (!uc.empty ());
		return uc;
	}
	
	void Gic::initialize_invariant (Cube uc) {
		assert (inv_.size () == 0);
		if (forward_){
			assert (inv_solver_ != NULL);
			uc.insert (uc.begin(), inv_solver_->get_flag ());
			inv_push (uc);
		}
		else
			inv_push (bad_);
	}
	
	bool Gic::invariant_check(){
		if (inv_solver_ == NULL){
			inv_solver_ = new InvSolver ();
			inv_solver_->add_transition ();
		}
		
		if (forward_){
			for (auto it = inv_.begin(); it != inv_.end()); ++it){
				if (inv_solver_->solve_with_assumption (*it))
					return false;
			}
			return true;
		}
		else{
			for (auto it = inv_.begin(); it != inv_.end()); ++it){
				if (inv_solver_->solve_with_assumption (inv_prime (*it))) //to be done
					return false;
			}
			return true;
		}
		return false;
	}
	
	Assignment& Gic::inv_prime (Assignment& cu){
		Assignment res;
		auto it = cu.begin();
		it ++;
		for (; it != cu.end(); ++it)
			res.push_back (model_->prime (*it));
		return res;
	} 


	void Gic::renew_invariant (Cube uc){
		if (forward_){
			inv_.clear();
			assert (inv_solver_ != NULL);
			uc.insert (uc.begin(), inv_solver_->get_flag ());
			inv_push (uc);
			//not finished
		}
		else{
			inv_.clear ();
			inv_push (bad_);
		}
		//MORE efficient algorithm is NEEDED!
	}
	
	void Gic::update_invariant (Cube uc){
		assert (inv_solver_ != NULL);
		uc.insert (uc.begin(), inv_solver_->get_flag ());
		inv_push (uc);
	}
	
	void Gic::update_bad (State* t) {
		bads_.push_back (t);
		add_bad_to_solver (t->s()); 
	}
	
	void Gic::inv_push(Cube& uc){
		inv_flag.push_back(uc[0]);
		inv_.push_back(uc);
		Clause temp;
		auto it = uc.begin();
		it++;
		for (;it != uc.end();it++)
			temp.push_back (model_->prime(-(*it)));
		inv_solver_->add_clause(temp);     //add !uc as clause to solver
	}

	void Gic::inv_push(int bad){
		Clause temp;
		temp.push_back(inv_solver_->get_flag ());
		temp.push_back(-(bad->s())[0]);     //?unsure
		inv_solver_->add_clause(temp);     //add !uc as clause to solver
	}


	void Gic::add_bad_to_solver (Cube& st){
		int flag = solver_->get_flag ();
		int new_bad = solver_->get_flag ();
		solver_->add_equivalence (-new_bad, -bad_, -flag);
		Clause& tmp;
		tmp.push_back (flag);
		for (auto it = st.begin (); it != st.end(); ++it){
			tmp.push_back (-(*st));
			solver_->add_clause (-flag, *it);
		}
		solver_->add_clause (tmp);
	}
	
	void Gic::update_init (State* t) {
		inits_.push_back (t);
		add_init_to_solver (t); 
	}
	
	void Gic::add_init_to_solver (Cube& st){
		int flag = solver_->get_flag ();
		int new_init = solver_->get_flag ();
		//int init_flag = get_init_flag (); //done in initialization, need to add equivalence of init_flag and init_
		set_init_flag (new_init);
		
		solver_->add_equivalence (-new_init, -init_flag, -flag);
		Clause& tmp;
		tmp.push_back (flag);
		for (auto it = st.begin (); it != st.end(); ++it){
			tmp.push_back (-(*st));
			solver_->add_clause (-flag, *it);
		}
		solver_->add_clause (tmp);
	}

	void set_init_flag (new_init){
		init_->s().clear();
		init_->s().push_back(new_init);
	}
	State* Gic::get_new_state (){
		Assignment st = inv_solver_->get_state (forward_);
		std::pair<Assignment, Assignment> pa = state_pair (st);
		State* res = new State (s, pa.first, pa.second);
		
		return res;
	}
	
	Assignment& Gic::get_partial (State* t){//more than one implementation
		if (forward_){
			assert (!sat_solve (t->all(), -bad));
		}
		else{
			return t->s ();
		}	
		return get_uc (); 
	}
	
}	
