
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
		if (sat_solve (init_, bad_))  //to be done
			return true;
		initialize_invariant (get_uc ());  //to be done
					
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
		if (sat_solve (init_, bad_))  //to be done
			return true;
		initialize_invariant (get_uc ());  //to be done
					
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
	bool Gic::sat_solve (State* start, State* next);	
	
	
	

}	
