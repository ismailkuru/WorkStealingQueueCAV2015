

const ownerThread :TID;
var T:variable;
var H:variable;


var tasks :variable;
const unique NULL :int ;
const unique EMPTY : int;
const unique ABORT : int;


procedure pop_head_ls_tail() returns (result:int){ // checked

  var local_tail:int;
  var local_head:int;
  var local_tail_version:int ;
  var local_head_version : int ;
  var local_tail_tmp:int;
  
  var ret_task:int;
  var head_changed:bool;
 
 
	 atomic{
	 
		assume tid == ownerThread;

		call local_tail_tmp := read(T);
		local_tail := local_tail_tmp -1 ;
		
		//update global T
		call write(T, local_tail);
		call drain_last();
		
	 }
 
	 atomic{
		
		assume tid == ownerThread;
		// mover check assertions
		assert local_tail == T.value;
		call local_head := read(H);		
			
		//Execution path distinguishing predicate: 
		assume local_head < local_tail;
	 
	 }
 
	 atomic{
	 
		 assume tid == ownerThread;
		// mover check assertions 
		assert local_tail == T.value;
		
		call ret_task := read_from_ptr (tasks, local_tail);
		assume local_head < local_tail;
	 
	 }
 
 
	 atomic{
		assume tid == ownerThread;
		// mover check assertions 
		assert local_tail == T.value;
		
		// correctness specification
		assert ret_task >0 ;
		result := ret_task;
		
		
		assume local_head < local_tail;
		return;
	 }
 

}



procedure pop_head_eq_tail_suc() returns(result : int ){

  var local_tail:int;
  var local_head:int;
  var local_tail_version:int ;
  var local_head_version : int ;
  var local_head_version_tmp:int;
  var local_tail_version_tmp:int ;
  var local_tail_tmp:int;

  var ret_task:int;
  var head_changed:bool;

  
	atomic{
		assume tid == ownerThread;
		call local_tail_tmp := read( T);
		local_tail := local_tail_tmp -1 ;
		// Write to global tail 
		call write(T, local_tail);
		call drain_last();
	
	}
	
	atomic{
		assume tid == ownerThread;
		//Ask Serdar : Should we do the abstraction you did in this phase, 
		//after this phase ?	
		assert T.value == local_tail;
		call local_head := read(H);
		assume local_head == local_tail;
		
	}
	 
	atomic{
		assume tid == ownerThread;
		assert T.value == local_tail;
	
		call ret_task := read_from_ptr(tasks, local_tail);	
				
		assume local_head == local_tail;
		
	}
	 	 		
	atomic{
		assume tid == ownerThread;
		assume local_head == local_tail;
		assume local_head == H.value ;
		
		assert ret_task >0;// correctness specification
		
		assert T.value == local_tail;	
		
		
		//Update global head
		call write(H, local_head + 1 );
		call drain_last();
		//Update global tail T
		call write(T, local_head + 1 );	
		call drain_last();
		
		result := ret_task;
		assume local_head == local_tail;
		
		return;
	}

	 

}



procedure pop_head_gt_tail() returns(result :int){

  var local_tail:int;
  var local_head:int;
  var local_tail_version:int ;
  var local_head_version : int ;
  var local_tail_tmp:int;
  var ret_task:int;
  var head_changed:bool;


	atomic{
	 assume tid == ownerThread;
		call  local_tail_tmp := read(T);
		local_tail := local_tail_tmp -1  ;
	
		call write(T,local_tail );
		call drain_last();
		//update global T
	
	 }
 
	 // No need to check the version number of H , it is already non-suc execution
	 atomic{
		 assume tid == ownerThread;
		// mover check assertions
		assert local_tail == T.value;
		
		call local_head := read(H);
			
		//Execution path distinguishing predicate: 
		assume  local_tail < local_head;
	 }
	 atomic{

		 assume tid == ownerThread;
		   assert local_tail == T.value;
		  call write(T, local_head );
		  call drain_last();	 
		
		
		assume local_tail < local_head;
	 }
	 
	 atomic{
	 assume tid == ownerThread;
		assume local_tail < local_head ;
		result := EMPTY;
		return;
	 }

}

procedure pop_head_eq_tail_not_suc() returns (result :int){


var local_tail:int;
  var local_head:int;
  var local_tail_version:int ;
  var local_head_version : int ;
  var local_head_version_tmp:int;
  var local_tail_version_tmp:int ;
  var local_tail_tmp:int ;

  var ret_task:int;
  var head_changed:bool;

  
	atomic{
	assume tid == ownerThread;
	       call local_tail_tmp := read(T);
	       local_tail := local_tail_tmp -1 ;		
	       call write(T, local_tail);
	       call drain_last();
		// Write to global tail 
		
	}
	
	atomic{
		assume tid == ownerThread;
		//Ask Serdar : Should we do the abstraction you did in this phase, 
		//after this phase ?	
		assert T.value == local_tail;
	
		call local_head := read(H);
		assume local_head == local_tail;
		
	}
	 
	atomic{
		assume tid == ownerThread;
		assert T.value == local_tail;
	
		call ret_task := read_from_ptr(tasks, local_tail);
	
		assume local_head == local_tail;
		
	}
	 	 		
	atomic{
		assume tid == ownerThread;
		assume local_head == local_tail;
		assume local_head != H.value ;
		
		result := EMPTY;
		assume local_head == local_tail;
		
		return;
	}

	 

}

procedure steal_head_ls_tail_suc() returns(result :int){
	var local_tail:int;
	var local_head:int;
	var local_tail_version:int ;
	var local_head_version : int ;
	var local_head_version_tmp:int;
	var local_tail_version_tmp:int ;
	var local_tail_tmp:int;

	var ret_task : int ;
	
	atomic{	
		assume tid != ownerThread;
	 	call local_tail := read(T);
		
	}
	
	
	// Ask Serdar : Abstraction bu phase mi koyalim ?
	atomic{
	 assume tid != ownerThread;
		assert T.value >= local_tail;
		call local_head := read(H);
		assume local_head < local_tail;
	}
	
	
	atomic{
		assume tid != ownerThread;
		assert T.value >= local_tail;
		call ret_task := read_from_ptr(tasks, local_head );		
		assume local_head < local_tail;
	}
	
	atomic{
	
		assume tid != ownerThread;
		assume local_head == H.value;
		assert ret_task > 0;// CORRECTNESS SPECIFICATION
		
		call write(H, local_head +1);
		call drain_last();
		result := ret_task;
		assume local_head < local_tail;
		return;
		
	}
	
	
	
}

procedure steal_head_ls_tail_suc_not() returns(result :int){
	var local_tail:int;
	var local_head:int;
	var local_tail_version:int ;
	var local_head_version : int ;
	var local_head_version_tmp:int;
	var local_tail_version_tmp:int ;
	var ret_task : int ;
	
	atomic{	
		 assume tid != ownerThread;
		 call local_tail := read(T);
	}	
	// Ask Serdar : Abstraction
	atomic{
	
		assume tid != ownerThread;
		assert T.value >= local_tail;
		call local_head := read(H);
		assume local_head < local_tail;
	}
	
	
	atomic{
	
		assume tid != ownerThread;
		assert T.value >= local_tail;
		call ret_task := read_from_ptr (tasks, local_head );
		assume local_head < local_tail;
	}
	
	atomic{
		assume tid != ownerThread;
		assume local_head != H.value;
		result := ABORT;
		assume local_head < local_tail;
		return;
	}
	
	
	
}

procedure steal_head_ge_tail() returns(result :int){
	
	var local_tail:int;
	var local_head:int;
	var local_tail_version:int ;
	var local_head_version : int ;
	var local_head_version_tmp:int;
	var local_tail_version_tmp:int ;
	var ret_task : int ;
	

	atomic{
		 assume tid != ownerThread;
		 call local_tail := read(T);
	}
	
	atomic{
	
		 assume tid != ownerThread;
		assert local_tail <= T.value;
		call local_head := read(H);	
		assume local_head >= local_tail;
	}
	
	atomic{
	
	 assume tid != ownerThread;
		
		assert local_tail <= T.value;
		
		
		assume local_head >= local_tail;
		result := EMPTY;
		return;
	
	}




}




procedure put(tsk:int)
{
	var local_tail:int;
	var local_head:int;
	var local_tail_version:int ;
	var local_head_version : int ;
	var local_head_version_tmp:int;
	var local_tail_version_tmp:int ;
	var ret_task : int ;
	
	assume tsk > 0;
	
	atomic{
		assume tid == ownerThread;
		call local_tail := read(T);
		
	}
	atomic{	
		assume tid == ownerThread;
		call write_to_ptr(tasks, local_tail, tsk);
		call drain_last();
    }
	atomic{	  

		assume tid == ownerThread;
		assert local_tail == T.value;
		
		call write(T, local_tail + 1 );	
		call drain_last();
	}
     
    
}
