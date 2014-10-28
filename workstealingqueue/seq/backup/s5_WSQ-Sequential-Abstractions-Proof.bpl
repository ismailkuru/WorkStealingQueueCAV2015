

const ownerThread :TID;
var T:int;
var H:int;

var T_version:int;
var H_version :int;

var tasks : [int]int;
const unique NULL :int ;
const unique EMPTY : int;
const unique ABORT : int;


procedure pop_head_ls_tail() returns (result:int){

  var local_tail:int;
  var local_head:int;
  var local_tail_version:int ;
  var local_head_version : int ;
  
  
  var ret_task:int;
  var head_changed:bool;
 
 
	 atomic{
	 
		assume tid == ownerThread;
		
		local_tail := T -1 ;
		
		//aux
		local_tail_version := T_version;
		
		//update global T
		T:= local_tail;
		
		// Writes to global needs updating Global variable's version number
		local_tail_version := local_tail_version + 1;
		T_version := local_tail_version ;
	 
	 }
 
	 atomic{
		
		assume tid == ownerThread;
		// mover check assertions
		assert local_tail_version == T_version;
		assert local_tail == T;
		
		local_head := H;
		
		//Execution path split predicate: 
		assume local_head < local_tail;
	 
	 }
 
	 atomic{
	 
	 assume tid == ownerThread;
		// mover check assertions 
		assert local_tail_version == T_version;
		assert local_tail == T;
		
		ret_task := tasks[local_tail];
	 	assert ret_task > 0;
		
		assume local_head < local_tail;
		return ;	 
	 }
 /*
 
	 atomic{
		assume tid == ownerThread;
		// mover check assertions 
		assert local_tail_version == T_version;
		assert local_tail == T;
		
		// correctness specification
		assert ret_task >0 ;
		result := ret_task;
		
		
		assume local_head < local_tail;
		return;
	 }*/
 

}



procedure pop_head_eq_tail_suc() returns(result : int ){

  var local_tail:int;
  var local_head:int;
  var local_tail_version:int ;
  var local_head_version : int ;
  var local_head_version_tmp:int;
  var local_tail_version_tmp:int ;
  
  var ret_task:int;
  var head_changed:bool;

  
	atomic{
	assume tid == ownerThread;
		local_tail := T - 1;
		
		local_tail_version := T_version;
		
		// Write to global tail 
		T:= local_tail;
		// do the update on version number of global tail
		local_tail_version := local_tail_version + 1;
		T_version := local_tail_version ;
	}
	
	atomic{
		assume tid == ownerThread;
		//Ask Serdar : Should we do the abstraction you did in this phase, 
		//after this phase ?	
		assert T == local_tail;
		assert T_version == local_tail_version;
	
		// Abstracted : local_head := H;
		// Abstracted : local_head_version := H_version;
		havoc local_head ; havoc local_head_version;
		 assume local_head_version <= H_version;
	 	if(*){assume local_head_version == H_version;
			    local_head := H;
		}else{assume local_head_version != H_version;}
		
		assume local_head == local_tail;
		
	}
	 
	atomic{
		assume tid == ownerThread;
		assert T == local_tail;
		assert T_version == local_tail_version;
	
		
		ret_task := tasks[local_tail];
		
		assume local_head == local_tail;
		
	}
	 	 		
	atomic{
		assume tid == ownerThread;
		assume local_head == local_tail;
		assume local_head == H ;
		assume local_head_version == H_version;
		
		assert ret_task >0;
		
		assert T == local_tail;
		assert T_version == local_tail_version;
		
		
		
		//Update global head
		H:= local_head + 1;
		// Update version num of global variable H
		local_head_version_tmp := H_version;
		H_version := local_head_version_tmp + 1;
	
		
		//Update global tail T	
		T:= local_head + 1;
		
		// Update the version number of global T
		local_tail_version_tmp := T_version ;
		T_version := local_tail_version_tmp + 1;
				
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
  var ret_task:int;
  var head_changed:bool;


	atomic{
	 assume tid == ownerThread;
		local_tail := T -1 ;
		
		//update global T
		T:= local_tail;
		//aux
		local_tail_version := T_version;
		local_tail_version := local_tail_version + 1;
		
		// Writes to global needs updating Global variable's version number
		T_version := local_tail_version ;
	 
	 }
 
	 // No need to check the version number of H , it is already non-suc execution
	 atomic{
		assume tid == ownerThread;
		// mover check assertions
		assert local_tail_version == T_version;
		assert local_tail == T;
		
		local_head := H;
		
		//Execution path distinguishing predicate: 
		assume  local_tail < local_head;
		
	 }
	 atomic{
		assume tid == ownerThread;
		assert local_tail == T;
		assert local_tail_version == T_version;
		T:= local_head;
	 
		local_tail_version := T_version;
		local_tail_version := local_tail_version + 1;
		T_version := local_tail_version;
		
		
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
  
  var ret_task:int;
  var head_changed:bool;

  
	atomic{
	assume tid == ownerThread;
		local_tail := T - 1;
		
		local_tail_version := T_version;
		
		// Write to global tail 
		T:= local_tail;
		// do the update on version number of global tail
		local_tail_version := local_tail_version + 1;
		T_version := local_tail_version ;
	}
	
	atomic{
	assume tid == ownerThread;
	//Ask Serdar : Should we do the abstraction you did in this phase, 
	//after this phase ?	
		assert T == local_tail;
		assert T_version == local_tail_version;
	
	//	local_head := H;
	//	local_head_version := H_version;
		havoc local_head ; havoc local_head_version;
		assume local_head_version <= H_version;
		if(*){
			assume local_head_version == H_version ; local_head := H;
		}
		else{
			assume local_head_version != H_version;

		}
		assume local_head == local_tail;
		
	}
	 
	atomic{
	assume tid == ownerThread;
		assert T == local_tail;
		assert T_version == local_tail_version;
	
		
		ret_task := tasks[local_tail];
		
		assume local_head == local_tail;
		
	}
	 	 		
	atomic{
	assume tid == ownerThread;
		assume local_head == local_tail;
		
		assume local_head != H ;
		assume local_head_version != H_version;
		
		//assert T == local_tail;
		//assert T_version == local_tail_version;
		
		
		result := EMPTY;
		assume local_head == local_tail;
		
		return;
	}

	 

}




procedure steal() returns (result: int)
{
  var t: int;
  var h: int;
  var tsk : int;
  var tmp_h_v : int;
  var h_v: int;

    atomic  {  

	    assume tid != ownerThread;
            havoc h; havoc h_v; assume h_v <= H_version;
            havoc tsk;
            if (*) {
				assume h_v == H_version; 
				h := H;
				assume h<T;
				tsk := tasks[h]; 
			}
            else { assume h_v != H_version; }
			
		
	}

    atomic {
         assume tid != ownerThread;
         // assert H < T;
         assume (h_v == H_version);
         H := h+1;

         tmp_h_v := H_version;
         tmp_h_v := tmp_h_v + 1;
         H_version := tmp_h_v;
    }

    result := tsk;
}



/*
procedure steal_head_ls_tail_suc() returns(result :int){
	var local_tail:int;
	var local_head:int;
	var local_tail_version:int ;
	var local_head_version : int ;
	var local_head_version_tmp:int;
	var local_tail_version_tmp:int ;
	var ret_task : int ;
	
	atomic{	
	 	assume tid != ownerThread;
		local_tail := T;
		local_tail_version := T_version;
	}
	
	
	// Ask Serdar : Abstraction bu phase mi koyalim ?
	atomic{
		assume tid != ownerThread;
		//Comes from first block ! assert T >= local_tail;
	 // Comes from first block ! assert T_version >= local_tail_version;
		
		
		havoc local_head ; havoc local_head_version;
		
		
		assume local_head_version <= H_version;
		     
		if(*){
			assume local_head_version == H_version;
			local_head := H;
			assume local_head < T ;
			
		}
		else{assume local_head_version != H_version;}
		
		assume local_head < local_tail;
	}
	
	
	atomic{
		assume tid != ownerThread;
		assert T >= local_tail;
		assert T_version >= local_tail_version;
			
		ret_task := tasks[local_head];
		assume local_head < local_tail;
	}
	
	atomic{
	
		assume tid != ownerThread;
		assume local_head == H;
		assume local_head_version == H_version;
		assert ret_task > 0;
		H:= local_head + 1;
		
		local_head_version_tmp := H_version;
		local_head_version_tmp := local_head_version_tmp + 1;
		H_version := local_head_version_tmp;
		
		result := ret_task;
		
		assume local_head < local_tail;
		return;
		
	}
	
	
	
}*/


procedure steal_head_ls_tail_suc_not() returns(result :int){
	var local_tail:int;
	var local_head:int;
	var local_tail_version:int ;
	var local_head_version : int ;
	var local_head_version_tmp:int;
	var local_tail_version_tmp:int ;
	var ret_task : int ;

	havoc local_head ;
	havoc local_tail;
	result := ABORT;
	return;
	
	
	
}

procedure steal_head_ge_tail() returns(result :int){
	
	var local_tail:int;
	var local_head:int;
	var local_tail_version:int ;
	var local_head_version : int ;
	var local_head_version_tmp:int;
	var local_tail_version_tmp:int ;
	var ret_task : int ;
	havoc local_head ;
	havoc local_tail;
	result := EMPTY;
	return;

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
		
		local_tail := T;
		local_tail_version := T_version;
	}
	atomic{	
		assume tid == ownerThread;
		tasks[local_tail] := tsk;
		
    }
	atomic{	  

		assume tid == ownerThread;
		assert local_tail == T;
		assert local_tail_version == T_version;
		T := local_tail + 1;
			
		local_tail_version_tmp := T_version;
		local_tail_version_tmp := local_tail_version_tmp + 1;
		T_version := local_tail_version;
	}
     
    
}
