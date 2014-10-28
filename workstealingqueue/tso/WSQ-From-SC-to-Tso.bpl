

const ownerThread :TID;
const unique T:variable;
const unique H:variable;
const unique tasks : variable;
const unique NULL :int ;
const unique ABORT:int ;

// Auxiliary variables : version numbers 
var T_version:int;
var H_version:int;

procedure pop_head_ls_tail() returns (result: int)// pop1
{
  var local_tail: int;
  var local_tail_tmp:int ;
  var local_head: int;
  var tail_version:int;
  var head_version:int;
  var local_head_version:int;
  var tail_index_first:int;
  var tail_index_second:int;

  atomic{
	assume tid == ownerThread;
  	call local_tail_tmp := read(T);
  	local_tail := local_tail_tmp -1 ;

 	tail_version := T_version;
	tail_version := tail_version + 1;
	call tail_index_first := write(T, local_tail);
  	
	T_version := tail_version;
  }
  atomic{
	assume tid == ownerThread;
	if(*){call isAtHeadAndDrain(tail_index_first);}
  } 
  atomic{
	assume tid == ownerThread;
	assert tail_version == T_version;
	assert local_tail == T.value;	
	call local_head := read(H);
	head_version := H_version;
	assume local_head < local_tail;		
  }
  atomic{
	assume tid == ownerThread;
	assume local_head < local_tail;
	if(*){call isAtHeadAndDrain(tail_index_first);}
  }
 
    atomic  {  
      assume tid == ownerThread;
      assert tail_version == T_version;
      assert local_tail == T.value;
      call result := read_from_ptr(tasks, local_tail);
      assert result  > 0;
      assume local_head < local_tail;
      return;
    }
}

procedure pop_head_eq_tail_suc() returns (result: int) // pop2
{
  var local_tail: int;
  var local_tail_tmp:int ;
  var local_head: int;
  var tail_version:int;
  var head_version:int;
  var local_head_version:int;
  var tail_index_first:int;
  var tail_index_second:int;

  atomic{
	assume tid == ownerThread;
  	call local_tail_tmp := read(T);
  	local_tail := local_tail_tmp -1 ;

 	tail_version := T_version;
	tail_version := tail_version + 1;
	call tail_index_first := write(T, local_tail);
  	
	T_version := tail_version;
  }

  // D1 Action
  atomic{
	assume tid == ownerThread;
	if(*){call isAtHeadAndDrain(tail_index_first);}
  }

 atomic{
	assume tid == ownerThread;
	assert tail_version == T_version;
	assert local_tail == T.value;
	assert result > 0;	
	call local_head := read(H);
	head_version := H_version;
	assume local_head == local_tail;	
	


 }
 atomic{
	assume tid == ownerThread;
	assume local_head == local_tail;
	if(*){call isAtHeadAndDrain(tail_index_first);}
 }

 atomic{
	assume tid == ownerThread;	
	assert tail_version == T_version;
	assert T.value == local_tail;
	call result := read_from_ptr(tasks, local_tail);
	
	//correctness specification
	assert result > 0;
 }
  // D1 Action


 atomic{
	assume tid == ownerThread;
	assume local_head == local_tail;
	if(*){call isAtHeadAndDrain(tail_index_first);}

 }
  atomic  {
	assume local_head == local_tail;
	assume tid == ownerThread;
	assert result > 0;
	assert tail_version == T_version;
        assert local_tail == T.value;
	call tail_index_second:= write(T, local_head + 1);

  }

  atomic{
	assume local_head == local_tail;
	assume tid == ownerThread;
	if(*){call isAtHeadAndDrain(tail_index_first);}
  }

  atomic{
	assume local_head == local_tail;
	assume tid == ownerThread;
	assert (tail_index_second==ThreadPool[ownerThread].wb_head ==>
	       T_version == tail_version &&
	       local_tail == T.value
	       );
	if(*){call isAtHeadAndDrain(tail_index_second);}
 }

 atomic{
	assume IsBufferEmpty(ownerThread,ThreadPool);
	assume ownerThread == tid;
	assume local_head == H.value;
	assume H_version == head_version;
	local_head := local_head + 1;
	
	local_head_version := H_version;
	local_head_version := local_head_version + 1;
	H.value := local_head;
	H_version := local_head_version;
	return;
 }

}

procedure pop_head_eq_tail_not_suc() returns (result: int)
{
 var local_tail: int;
  var local_tail_tmp:int ;
  var local_head: int;
  var tail_version:int;
  var head_version:int;
  var local_head_version:int;
  var tail_index_first:int;
  var tail_index_second:int;

  atomic{
	assume tid == ownerThread;
  	call local_tail_tmp := read(T);
  	local_tail := local_tail_tmp -1 ;

 	tail_version := T_version;
	tail_version := tail_version + 1;
	call tail_index_first := write(T, local_tail);
  	
	T_version := tail_version;
  }

 atomic{
	assume tid == ownerThread;
	if(*){	
	 call isAtHeadAndDrain(tail_index_first);
	}


}

 atomic  {
 	assume tid == ownerThread;
    assert local_tail == T.value;
    call result := read_from_ptr(tasks,local_tail);
  }

 atomic{
	assume tid == ownerThread;

	if(*){
      		call isAtHeadAndDrain(tail_index_first);
	}
}

 atomic  {
    assume tid == ownerThread;
    assert local_tail == T.value;
    call local_head := read(H);
    head_version := H_version;
    assume local_head == local_tail;
  }
 atomic{
	assume tid == ownerThread; 
 	assume local_head == local_tail;
 	if(*){call isAtHeadAndDrain(tail_index_first);}
}
 atomic  {  
     assume tid == ownerThread;	 
     assert IsBufferEmpty(ownerThread, ThreadPool); // Is buffer empty ?
     assume local_head != H.value ;
     result := NULL;
     return;
  }
}
procedure pop_head_gt_tail() returns (result: int){

  var local_tail: int;
  var local_tail_tmp:int ;
  var local_head: int;
  var tail_version:int;
  var head_version:int;
  var local_head_version:int;
  var tail_index_first:int;
  var tail_index_second:int;

  atomic{
	assume tid == ownerThread;
  	call local_tail_tmp := read(T);
  	local_tail := local_tail_tmp -1 ;

 	tail_version := T_version;
	tail_version := tail_version + 1;
	call tail_index_first := write(T, local_tail);
  	
	T_version := tail_version;
  }

 atomic{
	assume tid == ownerThread;
	if(*){call isAtHeadAndDrain(tail_index_first);}
}

  atomic  {  
  	  assume tid == ownerThread;
        assert local_tail == T.value;
        call local_head := read(H);
	head_version := H_version;
        assume local_tail < local_head; 
  }        
  

 atomic{
	assume tid == ownerThread; 
	assume local_tail < local_head;
	 if(*){call isAtHeadAndDrain(tail_index_first);}
}

  atomic  {  
  	   assume tid == ownerThread;
  	 assert local_tail == T.value;
     	 assume local_tail < local_head;
	 call tail_index_second :=  write(T,local_head);

  }

// D1:

 atomic{
	assume tid == ownerThread;
	assume local_tail < local_head;
	if(*){call isAtHeadAndDrain(tail_index_first);}
	
 }

//D2:
atomic{
	assume tid == ownerThread;
	assume local_tail < local_head;
	assert (tail_index_second == ThreadPool[ownerThread].wb_head ==>
	        local_tail == T.value &&
		tail_version == T_version
	);
	if(*){call isAtHeadAndDrain(tail_index_second);}
}

  atomic  {
  	  assume tid == ownerThread;
          result := NULL;
  }

}


procedure steal_head_ls_tail_succ() returns (result: int)
{
  var local_tail: int;
  var local_head: int;
  var head_version : int ;

  var tsk : int;

    atomic{

	assume tid != ownerThread;
 	call local_head := read(H);
	head_version := H_version ;
	
   }
	atomic{
		assume tid != ownerThread;
		 assume H_version == head_version ;
		call local_tail := read(T);
		assume local_head < local_tail;
	}
	
atomic{
	assume tid != ownerThread;
	assume local_head < local_tail;
	assume H_version == head_version;
	call tsk := read_from_ptr(tasks, local_head);
} 

	

    atomic{
       assume tid != ownerThread;
	   assume local_head < local_tail;
       assume head_version == H_version;
       assert IsBufferEmpty(tid,ThreadPool);
       H.value := local_head + 1;	
       head_version := H_version;
       head_version := head_version + 1;
       H_version := head_version;	 
    }

    result := tsk;
}
procedure steal_head_ls_tail_succ_not()returns (result : int ){

	var local_tail: int;
	var local_head: int;
	var tsk : int;
	var head_version : int;
 atomic{
	assume tid != ownerThread;
	call local_head := read(H);
	head_version := H_version ;
 }
 atomic{
	assume tid != ownerThread;
	call tsk := read_from_ptr(tasks, local_head);   //
	assume head_version != H_version;
	assume local_head != H.value;
 }	    	  
 atomic{	  
 	assume tid != ownerThread;
	assume head_version != H_version ;
	 assert IsBufferEmpty(tid,ThreadPool);
	assume local_head != H.value;

}
atomic{
	assume tid != ownerThread;
	result := ABORT;
}
}


procedure steal_head_ge_tail() returns (result: int){
 
  var local_tail: int;
  var local_head: int;

  assume tid != ownerThread ;
  call local_tail := read(T);
  call local_head := read(H);
  assume local_head >= local_tail;
  result := NULL;
}
 
procedure put(x:int)
{
	var local_tail:int;
	var tail_index_first:int;
	var tail_index_second:int;
	var tail_version : int;
	
	assume ownerThread == tid ;
	assume x > 0;
	assume(IsBufferEmpty(ownerThred,ThreadPool));

	atomic{
		assume ownerThread == tid;
		assume x >0 ;	
		call local_tail := read(T);
  		tail_version := T_version;
	}

	atomic{
		assume tid == ownerThread;
		assume x >0 ;
		call tail_index_first := write_to_ptr(tasks,local_tail, x);
	}
	atomic{
		assume tid == ownerThread;
		assume x >0 ;
		if(*){call isAtHeadAndDrain(tail_index_first);}
	}

	atomic{	assume tid == ownerThread;
		assert T.value == local_tail ;
		assert T_version == tail_version;
		call tail_index_second := write(T,local_tail + 1);
	}
	atomic{
		assume tid == ownerThread;
		assume x >0 ;
		if(*){call isAtHeadAndDrain(tail_index_first);}
	}
	atomic{
		assume tid == ownerThread;
		assert (
		       tail_index_second == ThreadPool[ownerThread].wb_head ==>
		       local_tail == T.value && T_version == tail_version

		);
		if(*){call isAtHeadAndDrain(tail_index_second);}
	}
}
