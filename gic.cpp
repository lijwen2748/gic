
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
		    
		    Assignment &t = get_assignment (); //get assignment in \neg C', to be done
		    if (sat_solve (t, bad)){
		    	Assignment &partial_t = get_partial (t,bad); //to be done
		    	update_bad (partial_t);      //to be done
		    	if (sat_solve (init_, bad))
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
		    
		    Assignment &t = get_assignment (); //get assignment in /neg C,to be done
		    if (sat_solve (init_, t)){
		    	Assignment &partial_t = get_partial (t,init_); //to be done
		    	update_init (partial_t);      //to be done
		    	if (sat_solve (init_, bad))
		    		return true;
		    	renew_invariant (bad); //two different implementations, to be done
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
		return uc;
	}
	
	void Gic::initialize_invariant (Cube& uc) {
		assert (inv_.size () == 0);
		if (forward_)
			inv_.push_back (uc);
		else
			inv_.push_back (bad_);
	}
	
	bool Gic::invariant_check(){
		if (forward_){
			for (auto it = inv_.begin(); it != inv_.end()); ++it){
				
			}
		}
		else{


		}
	}


	void Gic::renew_invariant (Cube& uc){
		if (forward_){
			inv_.clear();
			inv_.push_back (uc);
		}
		else{
			inv_.clear ();
			inv_.push_back (bad_);
		}
		//MORE efficient algorithm is NEEDED!
	}
	
	void Gic::update_invariant (Cube& uc){
		inv_.push_back (uc);
	}
	
	void Gic::update_bad (State* t) {
			//bads_.push_back (t);
			//TO BE DONE
	}
	
	void Gic::update_init (State* t) {
			//inits_.push_back (t);
			//TO BE DONE
	}
	

}	
