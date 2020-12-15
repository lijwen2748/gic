/*
    Copyright (C) 2018, Jianwen Li (lijwen2748@gmail.com), Iowa State University

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <https://www.gnu.org/licenses/>.
*/

/*
	Author: Jianwen Li
	Update Date: October 6, 2017
	Main Solver in GIC
*/

#ifndef MAIN_SOLVER_H
#define MAIN_SOLVER_H

#include "satsolver.h"
#include "data_structure.h"
#include "model.h"
#include "statistics.h"
#include <vector>
#include <assert.h>
#include <iostream>

namespace gic{

class MainSolver : public SATSolver 
{
	public:
		MainSolver (Model* model, Statistics* stats, const bool verbose = false);
		~MainSolver (){}
		
		
		inline bool solve_with_assumption (Assignment& st)
		{
			return solve_assumption (st);
		}
		

		void update_state_input (Assignment& inputs);
		
		inline int get_flag() {
				max_flag_++;
				return max_flag_;
			}
		
	private:
		//members
		int max_flag_;

		Model* model_;
		
		Statistics* stats_;

		int id_aiger_max_;
		
		//bool verbose_;
		
		//functions
		
		void shrink_model (Assignment& model, const bool forward, const bool partial);
		void try_reduce (Cube& cu);
};

}

#endif

