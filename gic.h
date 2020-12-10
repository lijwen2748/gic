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
		inline bool sat_solve (State* s, int bad) {
			stats_->count_main_solver_SAT_time_start ();
	        bool res = solver_->solve_with_assumption (s->s(), bad);
	        stats_->count_main_solver_SAT_time_end ();
	        return res;
		}
		
		bool sat_solve (State* start, State* next);
			
	};


}

#endif
