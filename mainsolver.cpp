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


#include "mainsolver.h"
#include "utility.h"

#include <algorithm>
using namespace std;

namespace gic
{
	
	MainSolver::MainSolver (Model* m, Statistics* stats, const bool verbose) : id_aiger_max_ (const_cast<Model*>(m)->max_id ())
	{
	    verbose_ = verbose;
	    stats_ = stats;
		model_ = m;
		if (max_flag_ == -1)
			max_flag_ = m->max_id() + 1;
	    //constraints
		for (int i = 0; i < m->outputs_start (); i ++)
			add_clause (m->element (i));
		//outputs
		for (int i = m->outputs_start (); i < m->latches_start (); i ++)
			add_clause (m->element (i));
		//latches
		for (int i = m->latches_start (); i < m->size (); i ++)
		    add_clause (m->element (i));
		max_flag_ = id_aiger_max_;
	}
	
	void MainSolver::update_state_input (Assignment& st){
		Assignment model = get_model ();
		for (int i = 0; i < model_->num_inputs (); i ++)
	    {
	        if (i >= model.size ())
	        {//the value is DON'T CARE, so we just set to 0
	            st.push_back (0);
	        }
	        else
	            st.push_back (model[i]);
	    }
	    
	}
	
	
}
