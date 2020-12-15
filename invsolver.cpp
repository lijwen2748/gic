#include "invsolver.h"
#include "utility.h"

#include <algorithm>
using namespace std;

namespace gic
{

	bool solve_with_assumption (const Assignment st)
	{
		Assignment temp;
		temp.insert(temp.begin(),st.begin(),st.end());
		temp.insert(temp.begin(),flag_assumption_.begin(),flag_assumption_.end());
		return solve_assumption (temp);
	}
		

    Assignment InvSolver::get_state (const bool forward)
	{
		Assignment model = get_model ();
		shrink_model (model, forward);
		return model;
	}

	void InvSolver::shrink_model (Assignment& model, const bool forward)
	{
	    Assignment res;
	    
	    for (int i = 0; i < model_->num_inputs (); i ++)
	    {
	        if (i >= model.size ())
	        {//the value is DON'T CARE, so we just set to 0
	            res.push_back (0);
	        }
	        else
	            res.push_back (model[i]);
	    }
	        
		if (forward)
		{
		    Assignment tmp;
		    tmp.resize (model_->num_latches (), 0);
		    for (int i = model_->num_inputs ()+1; i <= model_->num_inputs () + model_->num_latches (); i ++)
		    {
		    	
		    	int p = model_->prime (i);
		    	assert (p != 0);
		    	assert (model.size () > abs (p));
		    	
		    	int val = model[abs(p)-1];
		    	if (p == val)
		    		tmp[i-model_->num_inputs ()-1] = i;
		    	else
		    		tmp[i-model_->num_inputs ()-1] = -i;
		    }
		    
		    		    
		    for (int i = 0; i < tmp.size (); i ++)
		        res.push_back (tmp[i]);
		}
		model = res;
	}



}