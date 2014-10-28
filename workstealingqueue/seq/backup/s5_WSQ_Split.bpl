var tasks: [int]int;
var H: int;
var H_version: int;
var T: int;
var T_version: int;

const ownerThread: TID;
const unique NULL :int ;
const unique EMPTY : int ;
const unique ABORT: int ;


procedure steal_head_ge_tail() returns (result: int){
  var local_tail: int;
  var local_head: int;
  havoc local_head; // abstracted from h := H;
  havoc local_tail; // abstracted from t := T;
  // skip; // abstracted from assume h >= t;
  result := EMPTY;
}
procedure steal_head_ls_tail_succ_not()returns (result : int ){
	  
  var local_tail: int;
  var local_head: int;
  var ret_task : int;
  var tmp_head_version : int;
  var local_head_version: int;

    atomic  {  

	    assume tid != ownerThread;
            havoc local_head; havoc local_head_version; assume local_head_version <= H_version;
            havoc ret_task;
            if (*) {
				assume local_head_version == H_version; 
				local_head := H;
				assume local_head<T;
				ret_task := tasks[local_head]; 
			}
            else { assume local_head_version != H_version; } 
			
		
	}

    atomic {
         assume tid != ownerThread;
         // assert H < T;
         assume (local_head_version != H_version);
        // H := local_head+1;

    	result := ABORT;
        // tmp_head_version := H_version;
        // tmp_head_version := tmp_head_version + 1;
        // H_version := tmp_head_version;
    }
	  
}

procedure steal_head_ls_tail_succ() returns (result: int)
{
  var local_tail: int;
  var local_head: int;
  var ret_task : int;
  var tmp_head_version : int;
  var local_head_version: int;

    atomic  {  

	    assume tid != ownerThread;
            havoc local_head; havoc local_head_version; assume local_head_version <= H_version;
            havoc ret_task;
            if (*) {
				assume local_head_version == H_version; 
				local_head := H;
				assume local_head<T;
				ret_task := tasks[local_head]; 
			}
            else { assume local_head_version != H_version; } 
			
		
	}

    atomic {
         assume tid != ownerThread;
         // assert H < T;
         assume (local_head_version == H_version);
         H := local_head+1;

         tmp_head_version := H_version;
         tmp_head_version := tmp_head_version + 1;
         H_version := tmp_head_version;
    }

    result := ret_task;
}

procedure push(ret_task: int)
{
    var local_tail: int;
    var local_tail_version: int;
    var tmp_tail_version: int;

    atomic  {  
		assume tid == ownerThread;
        local_tail := T;
        local_tail_version := T_version;
    }

    atomic  { 
		assume tid == ownerThread;
       		 tasks[local_tail] := ret_task;
    }

    atomic  { 	
		assume tid == ownerThread;
        assert local_tail == T;
        assert local_tail_version == T_version;
        T := local_tail + 1;
        
        tmp_tail_version := T_version;
        tmp_tail_version := tmp_tail_version + 1;
        T_version := tmp_tail_version;
    }
}

procedure pop_head_ls_tail() returns (result: int)
{
  var local_tail: int;
  var local_tail_version: int;
  var local_head: int;

  atomic  {  
  	  assume tid == ownerThread;
	  local_tail := T - 1;
          local_tail_version := T_version;

	  T := local_tail;
          local_tail_version := local_tail_version + 1;
          T_version := local_tail_version;
  }

  atomic  {
  	  assume tid == ownerThread;
          assert local_tail_version == T_version;
          assert local_tail == T;
          local_head := H;
          assume local_head < local_tail; // Propagated from below: THIS NEEDS ATTENTION, MAYBE NEW PROOF STEP.
  }

  atomic  {  
  	  assume tid == ownerThread;
          assert local_tail_version == T_version;
          assert local_tail == T;

	  result := tasks[local_tail];

          assume local_head < local_tail;
          return;
  }
}

procedure pop_head_eq_tail_suc() returns (result: int)
{
  var local_tail: int;
  var local_tail_version: int;
  var local_head_version: int;
  var tmp_head_version: int;
  var tmp_tail_version: int;
  var local_head: int;

  atomic  {  
  	  assume tid == ownerThread;
	  local_tail := T - 1;
          local_tail_version := T_version;

	  T := local_tail;
          local_tail_version := local_tail_version + 1;
          T_version := local_tail_version;
  }

  

  atomic  {
  	  assume tid == ownerThread;
          assert local_tail_version == T_version;
          assert local_tail == T;
          // h := H; h_v := H_v;
          havoc local_head; havoc local_head_version; assume local_head_version <= H_version;
          if (*) { assume local_head_version == H_version;local_head := H; } 
          else { assume local_head_version != H_version;}
          assume local_head == local_tail;
  }
atomic  {
		assume tid == ownerThread;
        assert local_tail_version == T_version;
        assert local_tail == T;
		result := tasks[local_tail];
		assume local_head == local_tail;
  }

  atomic  {  
  	  assume tid == ownerThread;
      assert local_tail_version == T_version;
      assert local_tail == T;
	  assume (local_head == H) && (local_head_version == H_version);
	  
	  
	  
	 local_head := local_head + 1;

	  assume local_head == local_tail;
	  
	  tmp_head_version := H_version;
	  tmp_head_version := tmp_head_version + 1;
          H := local_head;
	  H_version := tmp_head_version;

			  T:= local_head;
	  
	    tmp_tail_version := tmp_tail_version + 1;
		T_version := tmp_tail_version;
        T := local_head + 1;
		assume local_head == local_tail;
		return;
  }
}

procedure pop_head_gt_tail() returns (result: int){

  var local_tail: int;
  var local_tail_version: int;
  var local_head_version: int;
  var tmp_head_version: int;
  var tmp_tail_version: int;
  var local_head: int;


  atomic  {  
  	  assume tid == ownerThread;
	  local_tail := T - 1;
          local_tail_version := T_version;

	  T := local_tail;
          local_tail_version := local_tail_version + 1;
          T_version := local_tail_version;
  }

  atomic  {  
  	  assume tid == ownerThread;
          assert local_tail == T;
         local_head := H;
          assume local_tail < local_head; 
  }


  atomic  {  
  	  assume tid == ownerThread;
          assert local_tail == T;
          
	  T := local_head;

          local_tail_version := T_version;
          local_tail_version := local_tail_version + 1;
          T_version := local_tail_version;
		  
		  assume local_tail <local_head;
  }

  atomic  {
			assume local_tail < local_head;
          result := EMPTY;
  }

}

procedure pop_head_eq_tail_not_succ() returns (result: int)
{
  var local_tail: int;
  var local_tail_version: int;
  var local_head_version: int;
  var tmp_head_version: int;
  var tmp_tail_version: int;
  var local_head: int;

  atomic  {  
  	  assume tid == ownerThread;
	  local_tail := T - 1;
          local_tail_version := T_version;

	  T := local_tail;
          local_tail_version := local_tail_version + 1;
          T_version := local_tail_version;
  }

  

  atomic  {
  	  assume tid == ownerThread;
          assert local_tail_version == T_version;
          assert local_tail == T;
          // h := H; h_v := H_v;
          havoc local_head; havoc local_head_version; assume local_head_version <= H_version;
          if (*) { assume local_head_version == H_version; local_head := H; } 
          else { assume local_head_version != H_version;}
          assume local_head == local_tail;
  }
atomic  {
		assume tid == ownerThread;
        assert local_tail_version == T_version;
        assert local_tail == T;
		result := tasks[local_tail];
		assume local_head == local_tail;
  }

  atomic  {  
  	  assume tid == ownerThread;
      //assert t_v == T_v;
      //assert t == T;
	  assume (local_head != H) && (local_head_version != H_version);
	  
	  result := EMPTY;
	  assume local_head == local_tail;
		
		return;
  }
}