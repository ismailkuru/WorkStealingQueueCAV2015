var tasks: variable;
var H: variable;
var T: variable;

const ownerThread: TID;
const unique EMPTY : int ;
const unique ABORT: int ;


procedure steal_head_ge_tail() returns (result: int){
  var local_tail: int;
  var local_head: int;
  //havoc local_head; // abstracted from h := H;
  //havoc local_tail; // abstracted from t := T;
  // skip; // abstracted from assume h >= t;
    assume tid != ownerThread;
	
  call local_head := read(H);
  call local_tail := read(T);
  assume local_head >= local_tail;

  result := EMPTY;
}

procedure steal_head_ls_tail_succ_not()returns (result : int ){
	  
  var local_tail: int;
  var local_head: int;
  var ret_task : int;
  
    
	    assume tid != ownerThread;
		havoc  local_head ; havoc local_tail ;
		havoc ret_task;  	


	      assume tid != ownerThread;
         result := ABORT;
    
	  
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
        call local_head := read(H);
	    call local_tail := read(T);
	    assume local_head<local_tail;
		call ret_task := read_from_ptr(tasks, local_head);
			
		
	}

    atomic {
		assume tid != ownerThread;
		call write(H,local_head + 1);
		call drain_last();
    }

    result := ret_task;
}

procedure push(ret_task: int)
{
    var local_tail: int;
  
    atomic  {  
		assume tid == ownerThread;
		call local_tail := read(T);
       
       
    }

    atomic  { 
		assume tid == ownerThread;
		call write_to_ptr(tasks,local_tail,ret_task);
		call drain_last();
    }

    atomic  { 	
		assume tid == ownerThread;
        assert local_tail == T.value;
        call write(T, local_tail +1 );
		call drain_last();
    }
}

procedure pop_head_ls_tail() returns (result: int)
{
  var local_tail: int;
  var local_head: int;
  var local_tail_tmp :int ;

  atomic  {  
  	  assume tid == ownerThread;
	  call local_tail_tmp := read(T);
	  local_tail := local_tail_tmp -1 ;

	 call write(T,  local_tail );
	 call drain_last();
  }

  atomic  {
  	  assume tid == ownerThread;
          assert local_tail == T.value;
          call local_head := read(H);
	  assume local_head < local_tail; // Propagated from below: THIS NEEDS ATTENTION, MAYBE NEW PROOF STEP.
  }

  atomic  {  
  	  assume tid == ownerThread;
          assert local_tail == T.value;

	  call result := read_from_ptr (tasks, local_tail);

          assume local_head < local_tail;
          return;
  }
}

procedure pop_head_eq_tail_suc() returns (result: int)
{
  var local_tail: int;
  var local_head: int;
  var local_tail_tmp : int ;
  
  atomic  {  
  	  assume tid == ownerThread;
	 call  local_tail_tmp := read(T);
  	 local_tail := local_tail_tmp -1 ;
	 call write(T, local_tail );
	 call drain_last();
  }

  

  atomic  {
  	  assume tid == ownerThread;
          assert local_tail == T.value;
          havoc local_head;
         call local_head := read(H);
	 // if (*) { assume local_head_version == H_version;local_head := H; } 
         // else { assume local_head_version != H_version;}
          assume local_head == local_tail;
  }
atomic  {
	assume tid == ownerThread;
        assert local_tail == T.value;
	call result := read_from_ptr(tasks, local_tail);
	assume local_head == local_tail;
  }
atomic{
	assume tid == ownerThread;
	assume local_tail == local_head;
	assert local_tail == T.value;
	
	call write(T, local_head + 1);
	call drain_last();
}

  atomic  {  
  	assume tid == ownerThread;
      	assert local_tail == T.value;
	 assume local_head == H.value ;
	  
	  
	  
	 local_head := local_head + 1;

	  call write(H, local_head);
	  call drain_last();
	 
	  assume local_head == local_tail;
	  return;
  }
}

procedure pop_head_gt_tail() returns (result: int){

  var local_tail: int;
  var local_head: int;
  var local_tail_tmp : int ;


  atomic  {  
  	  assume tid == ownerThread;
	 call  local_tail_tmp := read(T);
  	 local_tail := local_tail_tmp -1 ;
	 call write(T, local_tail );
	 call drain_last();
  }

  atomic  {  
  	  assume tid == ownerThread;
          assert local_tail == T.value;
         //local_head := H;

	 call local_head := read(H);
          assume local_tail < local_head; 
  }


  atomic  {  
  	  assume tid == ownerThread;
          assert local_tail == T.value;
          call write(T, local_head);
	  call drain_last();
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
  var local_head: int;
  var local_tail_tmp : int ;


  atomic  {  
  	  assume tid == ownerThread;
	 call  local_tail_tmp := read(T);
  	 local_tail := local_tail_tmp -1 ;
	 call write(T, local_tail );
	 call drain_last();
  }

  

  atomic  {
  	  assume tid == ownerThread;
          assert local_tail == T.value;
	  call local_head := read(H);
          assume local_head == local_tail;
  }
atomic  {
	assume tid == ownerThread;
        assert local_tail == T.value;
	call result := read_from_ptr(tasks, local_tail);
	assume local_head == local_tail;
  }

  atomic  {  
  	  assume tid == ownerThread;
      //assert t_v == T_v;
      //assert t == T;
	  assume (local_head != H.value) ;
	  
	  result := EMPTY;
	  assume local_head == local_tail;
		
		return;
  }
}