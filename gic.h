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

		//members
		Statistics *stats_;
		std::ofstream* dot_; //for dot file

		State* init_;  // initial state
		int bad_;
		Model* model_;
		MainSolver *solver_;
		InvSolver *inv_solver_;
		
		State* last_;
		
		class InvariantElement{
		public:
			InvariantElement (Cube& c) : cu_(c), checked_(false){
			}
			inline bool has_checked () {return checked_;}
			inline void set_checked (bool val) {checked_ = val;}
			inline Cube& cube() {return cu_;}
		private:
			Cube cu_;
			bool checked_;
		};
		
		class Invariant{
		public:
			Invariant (){}
			inline void push_back (InvariantElement ele) {inv_.push_back (ele);}
			inline std::vector<InvariantElement>& inv () {return inv_;}
			inline int level_flag () {return level_flag_;}
			inline void set_level_flag (int val) {level_flag_ = val;}
			inline int size () {return inv_.size();}
			
			//operator overloading
			InvariantElement& operator [] (int id) {return inv_[id];}
		private:
			std::vector<InvariantElement> inv_;
			int level_flag_; //the flag for the level of the invariant
		};
		
		std::vector<Invariant> invariants_;
		

		/*****main function******/

		bool gic_check ();

		bool forward_gic_check ();

		
		
		inline bool sat_solve (Assignment& assumption){
			stats_->count_main_solver_SAT_time_start ();
	    	bool res = solver_->solve_with_assumption (assumption);
	    	stats_->count_main_solver_SAT_time_end ();
	    	return res;
		}

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
		
		bool inv_check (int bad);
		
		bool inv_check (State* t, int level);
		
		bool sat_solve (Assignment& st, int bad);

		bool sat_solve (State* start, State* next);
		
		bool inv_sat_solve (Assignment& st, int level);
		
		void inv_solver_add_clause_from_cube (Cube& uc, int level);
		
		void inv_solver_add_clause_from_cube (Cube& s);

		Cube get_uc (); 
		
		void mark_transition (State* start, State* next=NULL);
		
		
		State* get_state ();
		
		Assignment get_partial (State* t);
		void generate_evidence ();

	};


}

#endif
