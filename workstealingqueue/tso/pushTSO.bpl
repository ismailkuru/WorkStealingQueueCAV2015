
const ownerThread :TID;
const unique T:variable;
const unique H:variable;
const unique tasks : variable;
const unique NULL :int ;
const unique ABORT:int ;

// Auxiliary variables : version numbers 
var T_v:int;
var H_v:int;


invariant(T.addr < H.addr);
invariant(H.addr < 0);
invariant(tasks.addr > 0);
//invariant(AllBuffersEmptyForVar(H, ThreadPool));
//invariant(forall td :TID :: td != ownerThread ==> !ExistsInBuffer(T,td, ThreadPool));


function default_post_cond(old_head:int, old_tail:int, hd:int , tl:int)returns(bool);
axiom(forall oh,ot,h,t:int  :: {default_post_cond(oh ,ot ,h ,t)} t >= ot && h>=oh <==> default_post_cond(oh ,ot ,h ,t) );

procedure {:isatomic} {:ispublic false} read_head()returns(result:int){

	var HD:int;
	var TL:int;
	HD := ThreadPool[tid].wb_head;
	TL := ThreadPool[tid].wb_tail;
	
	if(*){
		assume (forall i:int :: HD<=i  && i< TL ==> 
			ThreadPool[tid].wb[i].addr != H.addr  );
		
		result := H.value;
		assert result == H.mostRecent;
	}
	else{
	
		assume HD < TL;
		havoc result;
		assume (exists i:int:: 
				               (HD<=i && i<TL &&
                                result == ThreadPool[tid].wb[i].value &&		
		                        H.addr == ThreadPool[tid].wb[i].addr &&
								(forall j:int:: (i<j&&j<TL) ==> H.addr != ThreadPool[tid].wb[j].addr)
					           )
			   );
		assert result == H.mostRecent;

	}
}


procedure {:isatomic} {:ispublic false} read_tail()returns(result:int){
	
	var HD:int;
	var TL:int;
	HD := ThreadPool[tid].wb_head;
	TL := ThreadPool[tid].wb_tail;
	
	if(*){
		assume (forall i:int :: HD<=i  && i< TL ==> 
			ThreadPool[tid].wb[i].addr != T.addr  );
		
		result := T.value;
		assert result == T.mostRecent;
		
	}
	else{
	
		assume HD < TL;
		havoc result;
		assume (exists i:int:: 
				               (HD<=i && i<TL &&
                                result == ThreadPool[tid].wb[i].value &&		
		                        T.addr == ThreadPool[tid].wb[i].addr &&
								(forall j:int:: (i<j&&j<TL) ==> T.addr != ThreadPool[tid].wb[j].addr)
					           )
			   );
		assert ( result == T.mostRecent);

	}
}
 
procedure put(x:int)
{
	var t:int;
	var ti1:int;
	var ti2:int;
	var t_v : int;
	var old_wb_head:int;
	var old_wb_tail:int;
	
	
	assume ownerThread == tid ;
	assume x > 0;
	atomic{
		assume ownerThread == tid;
		assume x >0 ;	
	
		old_wb_tail := ThreadPool[ownerThread].wb_tail;
		old_wb_head := ThreadPool[ownerThread].wb_head;
	
	}
	
	atomic{
		assume ownerThread == tid;
		assume x >0 ;	
		
	
		call t := read_tail();
  		
		assert t == T.mostRecent;
	}

	atomic{
		assume tid == ownerThread;
		assume x >0 ;
		assert t == T.mostRecent;
		call ti1 := write_to_ptr(tasks,t, x);
	}
	atomic{
		assume tid == ownerThread;
		assume x >0 ;
		assert t == T.mostRecent;
		if(*){call isAtHeadAndDrain(ti1);}
	}

	atomic{
		assume tid == ownerThread;
		assert T.value == t ;
		
		assert t == T.mostRecent;
		call ti2 := write(T,t + 1);
	}
	atomic{
		assume tid == ownerThread;
		assume x >0 ;
		assert t == T.mostRecent;
		if(*){call isAtHeadAndDrain(ti1);}
	}
	atomic{
		assume tid == ownerThread;
		assert (
		       ti2 == ThreadPool[ownerThread].wb_head ==>
		       t == T.value // ti1 drain edilen index (T update edildi bu thread tarafindan)

		);
		if(*){call isAtHeadAndDrain(ti2);}
	}
	
	atomic{
		assume tid == ownerThread;
		
		assert(ThreadPool[ownerThread].wb_head > ti1 
		        ==>  
			T.mostRecent == t && addr2variable[tasks.addr+t].mostRecent == x && addr2variable[tasks.addr+t].value == x );
			
		assert(ThreadPool[ownerThread].wb_head > ti2 ==> 
			T.value == t+1 && T.mostRecent == T.value );
		
		assert default_post_cond(old_wb_head, old_wb_tail,ThreadPool[ownerThread].wb_head, ThreadPool[ownerThread].wb_tail);
	
	}
}


/*
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
  	call local_tail_tmp := read_tail();
  	local_tail := local_tail_tmp -1 ;

 	tail_version := T_v;
	tail_version := tail_version + 1;
	call tail_index_first := write(T, local_tail);
  	
	T_v := tail_version;
  }
  atomic{
	assume tid == ownerThread;
	if(*){call isAtHeadAndDrain(tail_index_first);}
  } 
  atomic{
	assume tid == ownerThread;
	assert tail_version == T_v;
	assert local_tail == T.value;	
	call local_head := read_head();
	head_version := H_v;
	assume local_head < local_tail;		
  }
  atomic{
	assume tid == ownerThread;
	assume local_head < local_tail;
	if(*){call isAtHeadAndDrain(tail_index_first);}
  }
 
    atomic  {  
      assume tid == ownerThread;
      assert tail_version == T_v;
      assert local_tail == T.value;
      call result := read_from_ptr(tasks, local_tail);
      assert result  > 0;
      assume local_head < local_tail;
      return;
    }
}*/

/*
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
  	call local_tail_tmp := read_tail();
  	local_tail := local_tail_tmp -1 ;

 	tail_version := T_v;
	tail_version := tail_version + 1;
	call tail_index_first := write(T, local_tail);
  	
	T_v := tail_version;
  }

  // D1 Action
  atomic{
	assume tid == ownerThread;
	if(*){call isAtHeadAndDrain(tail_index_first);}
  }

 atomic{
	assume tid == ownerThread;
	assert tail_version == T_v;
	assert local_tail == T.value;
	assert result > 0;	
	call local_head := read_head();
	head_version := H_v;
	assume local_head == local_tail;	
	


 }
 atomic{
	assume tid == ownerThread;
	assume local_head == local_tail;
	if(*){call isAtHeadAndDrain(tail_index_first);}
 }

 atomic{
	assume tid == ownerThread;	
	assert tail_version == T_v;
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
	assert tail_version == T_v;
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
	       T_v == tail_version &&
	       local_tail == T.value
	       );
	if(*){call isAtHeadAndDrain(tail_index_second);}
 }

 atomic{
	assume IsBufferEmpty(ownerThread,ThreadPool);
	//assert !ExistsInBuffer(H,ownerThread,ThreadPool);
	//assert H.value == H.mostRecent;
	
	assume ownerThread == tid;
	assume local_head == H.value;
	assume H_v == head_version;
	local_head := local_head + 1;
	
	local_head_version := H_v;
	local_head_version := local_head_version + 1;
	H.value := local_head;
	H_v := local_head_version;
	return;
 }

}

*//*
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
  	call local_tail_tmp := read_tail();
  	local_tail := local_tail_tmp -1 ;

 	tail_version := T_v;
	tail_version := tail_version + 1;
	call tail_index_first := write(T, local_tail);
  	
	T_v := tail_version;
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
    call local_head := read_head();
    head_version := H_v;
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
}*//*
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
  	call local_tail_tmp := read_tail();
  	local_tail := local_tail_tmp -1 ;

 	tail_version := T_v;
	tail_version := tail_version + 1;
	call tail_index_first := write(T, local_tail);
  	
	T_v := tail_version;
  }

 atomic{
	assume tid == ownerThread;
	if(*){call isAtHeadAndDrain(tail_index_first);}
}

  atomic  {  
  	  assume tid == ownerThread;
        assert local_tail == T.value;
        call local_head := read_head();
	head_version := H_v;
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
		tail_version == T_v
	);
	if(*){call isAtHeadAndDrain(tail_index_second);}
}

  atomic  {
  	  assume tid == ownerThread;
          result := NULL;
  }

}*/
/*

procedure steal_head_ls_tail_succ() returns (result: int)
{
  var local_tail: int;
  var local_head: int;
  var head_version : int ;

  var tsk : int;

    atomic{

	assume tid != ownerThread;
 	call local_head := read_head();
	head_version := H_v ;
	
   }
	atomic{
		assume tid != ownerThread;
		 assume H_v == head_version ;
		call local_tail := read_tail();
		assume local_head < local_tail;
	}
	
atomic{
	assume tid != ownerThread;
	assume local_head < local_tail;
	assume H_v == head_version;
	call tsk := read_from_ptr(tasks, local_head);
} 

	

    atomic{
       assume tid != ownerThread;
	   assume local_head < local_tail;
       assume head_version == H_v;
       assert IsBufferEmpty(tid,ThreadPool);
       H.value := local_head + 1;	
       head_version := H_v;
       head_version := head_version + 1;
       H_v := head_version;	 
    }

    result := tsk;
}

*//*
procedure steal_head_ls_tail_succ_not()returns (result : int ){

	var local_tail: int;
	var local_head: int;
	var tsk : int;
	var head_version : int;
 atomic{
	assume tid != ownerThread;
	call local_head := read_head();
	head_version := H_v ;
 }
 atomic{
	assume tid != ownerThread;
	call tsk := read_from_ptr(tasks, local_head);   //
	assume head_version != H_v;
	assume local_head != H.value;
 }	    	  
 atomic{	  
 	assume tid != ownerThread;
	assume head_version != H_v ;
	assert IsBufferEmpty(tid,ThreadPool);
	assume local_head != H.value;

}
atomic{
	assume tid != ownerThread;
	result := ABORT;
}
}
*/
/*
procedure steal_head_ge_tail() returns (result: int){
 
  var local_tail: int;
  var local_head: int;

  assume tid != ownerThread ;
  call local_tail := read_tail();
  call local_head := read_head();
  assume local_head >= local_tail;
  result := NULL;
}
 
*/