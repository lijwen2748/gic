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
		vector<Cube> inv_;

		/*****function******/
		inline bool sat_solve (State* s, int bad) {
			stats_->count_main_solver_SAT_time_start ();
	        bool res = solver_->solve_with_assumption (s->s(), bad);
	        stats_->count_main_solver_SAT_time_end ();
	        return res;
		}
		
		bool sat_solve (State* start, State* next);
		
		bool invariant_check();

		Cube& get_uc (); 
		
		inline void update_bad (State* t) {
			//bads_.push_back (t);
			//TO BE DONE
		}
		inline void update_init (State* t) {
			//inits_.push_back (t);
			//TO BE DONE
		}
			
	};


}

#endif
