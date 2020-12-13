 #ifndef CHECKER_H
 #define CHECKER_H

namespace gic
{
	class Gic 
	{
	public:
		Gic (Model* model, Statistics& stats, std::ofstream* dot, bool forward = true, bool evidence = false, bool verbose = false);
		~Gic ();
		
		bool check (std::ofstream&);
		void print_evidence (std::ofstream&);
		
	protected:
		/*****data structure******/
		typedef vector<int> Cube;

		std::vector<Cube> inv_;

		typedef std::vector<int> Assignment;

		int init_flag;    //to assign initial flag 

		std::vector<int> inv_flag;
		/*****main function******/
		void gic_initialization ();

		bool gic_check ();

		bool forward_gic_check ();

		bool backward_gic_check ();


		/*****helper function******/

		inline bool sat_solve (State* s, int bad) {
			stats_->count_main_solver_SAT_time_start ();
	        bool res = solver_->solve_with_assumption (s->s(), bad);
	        stats_->count_main_solver_SAT_time_end ();
	        return res;
		}
		
		bool sat_solve (State* start, State* next);
		
		bool invariant_check();

		Cube& get_uc (); 

		void initialize_invariant (Cube uc);

		bool invariant_check();

		Assignment& inv_prime (Assignment& cu);

		void renew_invariant (Cube uc);

		void update_invariant (Cube uc);

		void update_bad (State* t);

		void add_bad_to_solver (Cube& st);

		void update_init (State* t);

		void add_init_to_solver (Cube& st);

		State* get_new_state ();

		Assignment& get_partial (State* t);
		
		void inv_push(Cube& uc);

		void inv_push(int bad);

		void set_init_flag (int new_init);
	};


}

#endif
