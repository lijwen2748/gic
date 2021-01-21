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
			vector<Clause> frame; //the last element in frame[i] is the flag
			//vector<int> flag_vec;
		};

		vector<Frame*> F_;

		set<int> increase_flag_;

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

		inline void add_frame_level(){
			frame_level_ = F_.size();
		}

		
		/*****helper function******/

		void gic_initialization ();

		void gic_finalization ();	

		bool immediate_satisfiable ();
		
		bool sat_solve (Assignment& st, int bad);

		bool sat_solve (State* start, State* next);

		bool sat_solve (State* start, Cube& next);
		
		//bool inv_sat_solve (Assignment& st, int level);
		
		//bool inv_sat_solve (State* s);
		
		void inv_solver_add_clause_from_cube (Cube& uc, int level);
		
		void inv_solver_add_clause_from_cube (Cube& s);

		Cube get_uc (SATSolver*); 

		Cube get_forward_uc (SATSolver*);
		
		void mark_transition (State* start, State* next=NULL);
		
		
		State* get_state ();

		std::pair<Assignment, Assignment> state_pair (const Assignment& st);
		
		void set_partial (State* s,State* t);

		void set_partial (State* s);

		bool inv_partial_solve (State* s,State* t);
		
		void remove_input_flag (Cube& uc);
		
		void add_invariant_to_solver (Invariant* inv);
		
		/*************backward*************/
		bool pdr_check ();
		void set_new_frame ();
		bool rec_block (State* c,int k);
		bool frame_is_equal (int& a, int& b);
		void add_mic_to_frame (Cube& mic);
		bool deep_check (State* t);

		bool inv_sat_solve (int frame_level, int not_bad);
		bool inv_sat_solve (int not_bad, State* t);
		bool inv_sat_solve (Cube& cu, int n);
		bool inv_sat_solve (int bad); 
		bool inv_sat_solve (State* s);
		bool inv_sat_solve (Cube& cu, Cube& t);
		bool inv_sat_solve (State* init, Cube& t);
		Cube get_mic (SATSolver* solver, State* t);
		bool try_reduce (Cube s, Cube t);
		bool in_initial (Cube &cu);
		Cube complement (Cube& cu1, Cube& cu2);
		
		void set_common (Cube& st);
		bool common_in_initial ();
		void update_common_with (State* s);
		bool inv_common_sat_solve (int not_bad, State* t);
		bool is_blocked (State* t);
		
		Assignment get_partial (State* t);
		void generate_evidence ();

	};


}

#endif
