 #ifndef GIC_H
 #define GIC_H

 
#include "data_structure.h"
#include "satsolver.h"
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
		std::vector<State*> states_;
		
		State* last_;
		
		Cube common_;
		int common_flag_;
		
		class InvariantElement{
		public:
			InvariantElement (Cube& c) : cu_(c), checked_(false){
			}
			inline bool has_checked () {return checked_;}
			inline void set_checked (bool val) {checked_ = val;}
			inline Cube& cube() {return cu_;}
			inline int size () {return cu_.size();}
			
			inline void print () {gic::print (cu_);}
			
			//operator overloading
			int& operator [] (int id) {return cu_[id];}
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
			
			inline void print () {
				for(auto it = inv_.begin(); it != inv_.end(); ++it){
					it->print();
				}
				std::cout<<"level_flag_ is" << level_flag_ << std::endl;
			}
			
			//operator overloading
			InvariantElement& operator [] (int id) {return inv_[id];}
		private:
			std::vector<InvariantElement> inv_;
			int level_flag_; //the flag for the level of the invariant
		};
		
		std::vector<Invariant> invariants_;
		
		struct Frame
		{
			std::vector<Clause> frame;  //additional clauses in this and previous frames
			InvSolver *frame_solver;
			//vector<int> flag_vec;
		};

		std::vector<Frame*> F_;

		std::set<int> increase_flag_;

		int frame_level_;
		

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
		
		bool sat_solve (Assignment& st, int bad);
		
		//bool inv_sat_solve (Assignment& st, int level);
		
		//bool inv_sat_solve (State* s);
		
		void inv_solver_add_clause_from_cube (Cube& uc, int level);
		
		void inv_solver_add_clause_from_cube (Cube& s);

		Cube get_uc (SATSolver*); 

		Cube get_forward_uc (SATSolver*);
		
		void mark_transition (State* start, State* next=NULL);
		
		
		State* get_state ();

		std::pair<Assignment, Assignment> state_pair (const Assignment& st);
		
		Cube get_predecessor (Cube& s);

		bool inv_partial_solve (State* F_state,Cube& s);
		
		void remove_input_flag (Cube& uc);
		
		void add_invariant_to_solver (Invariant* inv);
		
		/*************backward*************/
		bool pdr_check ();
		void set_new_frame ();
		bool rec_block (Cube& s,int k);
		bool frame_is_equal (int& i);
		void add_mic_to_frame (Cube& mic,int frame_level);
		bool deep_check (State* t);
		bool inv_solve (Cube& cu, Cube& t);
		
		bool inv_sat_solve (int frame_level, int not_bad);
		bool inv_sat_solve (Cube& s, int frame_level);
		bool inv_sat_solve (State* init, Cube& t);
		bool inv_sat_solve (Cube& cu, int n,int frame_level);
		bool inv_sat_solve (Cube& cu, Cube& t);
		bool inv_initial_solve (Cube& t); //if t is reachable from initial states
		
		Cube get_mic (SATSolver* solver, Cube& s,int& frame_level);
		bool try_reduce (Cube s, Cube t);
		bool in_initial (Cube &cu);
		Cube complement (Cube& cu1, Cube& cu2);
		
		void generalize_mic (Cube& s,int& frame_level);
		bool down (Cube& c, int& frame_level, Cube& required);
		bool is_sat_assuming (Cube& cu,int& frame_level);
		Cube get_intersection (Cube& a, Cube& b);
		void set_common (Cube& st);
		bool common_in_initial ();
		void update_common_with (State* s);
		bool inv_common_sat_solve (int not_bad, State* t);
		bool is_blocked (State* t);
		
		Assignment get_partial (State* t);
		void generate_evidence ();
		void print_frame ();
	};


}

#endif
