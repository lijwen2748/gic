 #ifndef GIC_H
 #define GIC_H

 
#include "data_structure.h"
#include "invsolver.h"
#include "mainsolver.h"
#include "model.h"
#include <assert.h>
#include "utility.h"
#include "statistics.h"
#include <fstream>
#include <algorithm>


namespace gic
{
	class Gic 
	{
	public:
		Gic (Model* model, Statistics& stats, std::ofstream* dot, bool forward = true, bool evidence = false, bool verbose = false);
		~Gic (){}
		
		bool check (std::ofstream&);
		inline void print_evidence (std::ofstream&) {} //to be done
		
	protected:
		/*****data structure******/
		//flag
		bool forward_;
		bool evidence_;
		bool verbose_;
		//varialbes related to flag in inv_
		int init_flag_;    //initialize initial state to a flag, only for backward GIC
		std::vector<Cube> inv_;

		//members
		Statistics *stats_;
		std::ofstream* dot_; //for dot file

		State* init_;  // initial state
		int bad_;
		std::vector<Assignment> bads_;
		std::vector<State*> inits_;
		Model* model_;
		MainSolver *solver_;
		InvSolver *inv_solver_;

		/*****main function******/

		bool gic_check ();

		bool forward_gic_check ();

		bool backward_gic_check ();

		/*inline function*/
		inline void create_inv_solver (){
			inv_solver_ = new InvSolver (model_, verbose_);
		}

		inline void delete_inv_solver (){
			delete inv_solver_;
			inv_solver_ = NULL;
		}

		
		/*****helper function******/

		void gic_initialization ();

		void gic_finalization ();	

		bool immediate_satisfiable ();
		
		bool sat_solve (Assignment& s, int bad);

		bool sat_solve (State* start, State* next);
		
		bool sat_solve (int init_flag, State* next);

		bool invariant_check();

		Cube& get_uc (); 

		void initialize_invariant (Cube& uc);

		Assignment& inv_prime (Assignment& cu);

		void renew_invariant (Cube& uc);

		void update_invariant (Cube& uc);

		void update_bad (Assignment& t);

		void add_bad_to_solver (Cube& st);

		void update_init (State* t);

		void add_init_to_solver (Cube& st);

		State* get_new_state ();

		std::pair<Assignment, Assignment> state_pair (const Assignment& st);

		Assignment& get_partial (State* t);
		
		void inv_push(Cube uc);

		void inv_push(int bad);

		void invsolver_add_flag_assumption ();

	};


}

#endif
