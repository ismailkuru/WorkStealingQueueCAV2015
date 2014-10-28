var tasks: [int]int;
var H: int;
var H_version: int;
var T: int;
var T_version: int;

var MAX_tail:int;
var MIN_head:int ;

const ownerThread: TID;
const unique NULL :int ;
const unique EMPTY : int ;
const unique ABORT: int ;




procedure steal_head_ge_tail() returns (result: int){
  var local_tail: int;
  var local_head: int;
  havoc local_head; 
  havoc local_tail; 
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
           
				assume ((local_head_version == H_version ) ==> (local_head < T &&
					local_head == H && tasks[local_head] == ret_task));
						
	}

    atomic {
         assume tid != ownerThread;
         assume (local_head_version != H_version);
       	result := ABORT;
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
    		assume ((local_head_version == H_version) ==> 
				(local_head == H && local_head < T && ret_task == tasks[local_head])); 
	
	}

    atomic {
         assume tid != ownerThread;
         assume (local_head_version == H_version);
		 
		 H := local_head+1;
//	    havoc MIN_head ;
	//	assume ((MIN_head <= H && !(tasks[MIN_head] >0)) && (forall i:int :: i>MIN_head && i<=H ==> tasks[i] > 0));

		 
		 tmp_head_version := H_version;
         tmp_head_version := tmp_head_version + 1;
         H_version := tmp_head_version;
    }

    result := ret_task;
    assert result > 0;
}

procedure push(ret_task: int) // 
{
    var local_tail: int;
	var local_head :int ;
    var local_tail_version: int;
    var tmp_tail_version: int;
	var local_max_tail : int ;
	assume ret_task >0;
	
	atomic  {  
		assume tid == ownerThread;
		local_tail := T;
	    local_tail_version := T_version;
		assume local_tail <= T;// Tail'e sadece ben yaziyorum 
	}

    atomic  { 
		
		assume tid == ownerThread;
		
		tasks[local_tail] := ret_task;
		assume local_tail == T; // Tail'e sadece ben yaziyorum 
		
		
	}

    atomic  { 	
		assume tid == ownerThread;
		assert local_tail <= T;
        assert local_tail_version == T_version;
		
        T := local_tail + 1;
	    
		
	//	havoc local_head ;
	//	assume local_head == H;
	//	assume local_tail + 1 >  local_head;
		
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
	 assert result > 0;
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
          havoc local_head; havoc local_head_version; assume local_head_version <= H_version;
    	  assume(local_head_version == H_version ==> local_head == H);
		  
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
	  
	  
	  assert result > 0;
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
  atomic{  
  	  assume tid == ownerThread;
          assert local_tail == T;
         local_head := H;
          assume local_tail < local_head; 
  }
  atomic{  
  	  assume tid == ownerThread;
      assert local_tail == T;
	
      T := local_head;
	
      local_tail_version := T_version;
      local_tail_version := local_tail_version + 1;
      T_version := local_tail_version;
		  
		  assume local_tail <local_head;
  }
  atomic{
			assume tid == ownerThread;
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
      havoc local_head; havoc local_head_version; assume local_head_version <= H_version;
    	 
      assume local_head_version == H_version  ==> local_head == H ;
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
      assume (local_head != H) && (local_head_version != H_version);
	  
	  result := EMPTY;
	  assume local_head == local_tail;
		
		return;
  }
}