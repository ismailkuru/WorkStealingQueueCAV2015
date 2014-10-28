
invariant (forall t:thread, i:int :: t.h_value_of_var[i]<=t.t_value_of_var[i]);
invariant (forall t:thread :: t.wb_tail >= t.wb_head);
invariant (forall idx:int , t:thread :: idx >= t.wb_head && idx< t.wb_tail ==> t.h_value_of_var[t.wb[idx].addr]  < t.t_value_of_var[t.wb[idx].addr]);

invariant (forall t:TID , v:variable, i:int  :: 
  (i >= ThreadPool[t].h_value_of_var[v.addr] &&  i < ThreadPool[t].t_value_of_var[v.addr] && v.dirty[tid])  
	==>
  (ThreadPool[t].indx_of_var[v.addr,i] >= ThreadPool[t].wb_head && ThreadPool[t].indx_of_var[v.addr,i] < ThreadPool[t].wb_tail ));
	
invariant (forall v1,v2:variable :: v1!= v2 <==> v1.addr != v2.addr);
invariant (forall t1,t2:TID :: ThreadPool[t1] != ThreadPool[t2] <==> t1 != t2);
//invariant(forall index_addr:int :: ref_to_variable[index_addr].value[ADDR]== index_addr);

record variable{

	value:int ; // value of variable : Note: ref type may be used
	addr:int; // addr of variable : Note: ref tpye may be used.
	ver:int ; // global version number of a variable

	dirty:[TID]bool; // is there is any write in any of buffer for this variable then it is false
	allocation:bool;
	
	valInbuffers:[TID]int ; // value of recent write in ThreadPool[tid]
	indxInbuffers:[TID]int; // index of recent value in ThreadPool[tid]
}


record assignment{
	addr:int;
	value:int ;
}

record thread{
	
	t_id : TID;
	wb_head:int;
	wb_tail:int;
	wb:[int]assignment;
	
	value_of_var:[int, int]int;// variabes to its values in thread tid
	h_value_of_var:[int]int; // h_value_of_var<=idx < t_value_of_var
	t_value_of_var:[int]int; //  h_value_of_var<=idx < t_value_of_var
	indx_of_var:[int,int]int; // addr , h_value_of_var<=idx < t_value_of_var ==> wb_head <= indx_int_thread_buf < wb_tail
	
}


var ThreadPool:[TID]thread;
var thread_local_to_variable:[int]variable;


procedure {:isatomic true} drain_last()

{
	
	
var bastakiAdres:int ;

bastakiAdres := ThreadPool[tid].wb[ThreadPool[tid].wb_head].addr;
	
assert (ThreadPool[tid].t_value_of_var[bastakiAdres] == ThreadPool[tid].h_value_of_var[bastakiAdres] +1);

assert ((ThreadPool[tid].wb_head + 1 ) == ThreadPool[tid].wb_tail);


assert thread_local_to_variable[bastakiAdres].dirty[tid];
assert 	ThreadPool[tid].indx_of_var[bastakiAdres,ThreadPool[tid].h_value_of_var[bastakiAdres]] == ThreadPool[tid].wb_head;
assert	ThreadPool[tid].indx_of_var[bastakiAdres,ThreadPool[tid].t_value_of_var[bastakiAdres]] == ThreadPool[tid].wb_tail;	
		
thread_local_to_variable[bastakiAdres].value := 
      ThreadPool[tid].value_of_var[bastakiAdres,ThreadPool[tid].h_value_of_var[bastakiAdres]];  
thread_local_to_variable[bastakiAdres].ver := 
    thread_local_to_variable[bastakiAdres].ver + 1;
thread_local_to_variable[bastakiAdres].dirty[tid] := false;

// Violates		
ThreadPool[tid].h_value_of_var[bastakiAdres] := ThreadPool[tid].h_value_of_var[bastakiAdres] + 1;
ThreadPool[tid].wb_head := ThreadPool[tid].wb_head + 1;
		
assert  ThreadPool[tid].h_value_of_var[bastakiAdres] == ThreadPool[tid].t_value_of_var[bastakiAdres]; 
assert  !thread_local_to_variable[bastakiAdres].dirty[tid];
assert 	ThreadPool[tid].wb_head == ThreadPool[tid].wb_tail;	
assert false;			
}

procedure {:isatomic true} write_to_ptr(taddr:variable, offset:int, sval:int){
	
	var as:assignment;
	var bastakiAdres :int;

	var oldH :int ;
	var oldT:int;


	
	assume offset >=0 ;
	bastakiAdres := taddr.addr+offset;
	assert ThreadPool[tid].wb_tail == ThreadPool[tid].wb_head ;
	assert ThreadPool[tid].t_value_of_var[bastakiAdres] == ThreadPool[tid].h_value_of_var[bastakiAdres];

	assert ThreadPool[tid].indx_of_var[bastakiAdres, ThreadPool[tid].h_value_of_var[bastakiAdres]] == ThreadPool[tid].wb_head ;
	assert ThreadPool[tid].indx_of_var[bastakiAdres, ThreadPool[tid].h_value_of_var[bastakiAdres]] == ThreadPool[tid].indx_of_var[bastakiAdres, ThreadPool[tid].t_value_of_var[bastakiAdres]];
	
	oldH := ThreadPool[tid].h_value_of_var[bastakiAdres];
	oldT := ThreadPool[tid].t_value_of_var[bastakiAdres];

	as.value := sval;
	as.addr := bastakiAdres;
	
	thread_local_to_variable[bastakiAdres].valInbuffers[tid] := sval;
	thread_local_to_variable[bastakiAdres].dirty[tid]:= true; // burada 0'inci adresten sonra her bir variable size'inda bu offsete kadar olan tum variable'lar dirty mi ?
	thread_local_to_variable[bastakiAdres].indxInbuffers[tid] := ThreadPool[tid].wb_tail;
	
	ThreadPool[tid].wb[ThreadPool[tid].wb_tail] := as;
	ThreadPool[tid].value_of_var[bastakiAdres,ThreadPool[tid].t_value_of_var[bastakiAdres]] := as.value;
	ThreadPool[tid].indx_of_var[bastakiAdres, ThreadPool[tid].t_value_of_var[bastakiAdres]] := ThreadPool[tid].wb_tail;
	
	
	
	////
	
	assert as.addr ==  bastakiAdres;
	assert as.value == sval;
	assert ThreadPool[tid].t_value_of_var[as.addr] == ThreadPool[tid].h_value_of_var[as.addr];
	
	
	assert ThreadPool[tid].indx_of_var[bastakiAdres,oldH] == ThreadPool[tid].wb_head ;	
	assert ThreadPool[tid].indx_of_var[bastakiAdres,oldT] == ThreadPool[tid].wb_tail ;
	
	ThreadPool[tid].t_value_of_var[bastakiAdres] := ThreadPool[tid].t_value_of_var[bastakiAdres]+1;
	
	ThreadPool[tid].wb_tail := ThreadPool[tid].wb_tail + 1;
	
	assert false;
}


procedure {:isatomic true} write(taddr:variable, sval : int){

	var as:assignment;
	var oldH :int ;
	var oldT:int;
	//assert ThreadPool[tid].wb_tail == ThreadPool[tid].wb_head ;
	//assert ThreadPool[tid].t_value_of_var[ThreadPool[tid].wb[ThreadPool[tid].wb_tail].addr] == ThreadPool[tid].t_value_of_var[ThreadPool[tid].wb[ThreadPool[tid].wb_tail].addr];
	
	assert ThreadPool[tid].wb_tail == ThreadPool[tid].wb_head ;
	assert ThreadPool[tid].t_value_of_var[taddr.addr] == ThreadPool[tid].h_value_of_var[taddr.addr];
	assert ThreadPool[tid].indx_of_var[taddr.addr, ThreadPool[tid].h_value_of_var[taddr.addr]] == ThreadPool[tid].wb_head ;
	assert ThreadPool[tid].indx_of_var[taddr.addr, ThreadPool[tid].h_value_of_var[taddr.addr]] == ThreadPool[tid].indx_of_var[taddr.addr, ThreadPool[tid].t_value_of_var[taddr.addr]];

	oldH := ThreadPool[tid].h_value_of_var[taddr.addr];
	oldT := ThreadPool[tid].t_value_of_var[taddr.addr];
	
	as.value := sval;
	as.addr := taddr.addr;
	
	taddr.valInbuffers[tid] :=  sval;
	taddr.dirty[tid] := true;
	taddr.indxInbuffers[tid] := ThreadPool[tid].wb_tail;

	ThreadPool[tid].wb[ ThreadPool[tid].wb_tail] := as;
	
	ThreadPool[tid].value_of_var[taddr.addr,ThreadPool[tid].t_value_of_var[taddr.addr]] := as.value;
	ThreadPool[tid].indx_of_var[taddr.addr,ThreadPool[tid].t_value_of_var[taddr.addr]] := ThreadPool[tid].wb_tail;

	assert as.addr == taddr.addr;
	assert as.value == sval;
	assert ThreadPool[tid].t_value_of_var[as.addr] == ThreadPool[tid].h_value_of_var[as.addr];
	
	
	assert ThreadPool[tid].indx_of_var[taddr.addr,oldH] == ThreadPool[tid].wb_head ;	
	assert ThreadPool[tid].indx_of_var[taddr.addr,oldT] == ThreadPool[tid].wb_tail ;
	
	ThreadPool[tid].t_value_of_var[taddr.addr] := ThreadPool[tid].t_value_of_var[taddr.addr]+1;
	
	ThreadPool[tid].wb_tail := ThreadPool[tid].wb_tail + 1;
	
	assert false;
}


procedure {:isatomic true} read_from_ptr(toRead:variable, offset:int) returns(result:int){

	
	if(*){
		//assume tid == recvThread || tid == senderThread;
		assume offset >= 0;
		assume ThreadPool[tid].t_value_of_var[toRead.addr] == ThreadPool[tid].h_value_of_var[ toRead.addr] ;
		assume ThreadPool[tid].wb_head == ThreadPool[tid].wb_tail;
		assume (!toRead.dirty[tid]);
		
		result := toRead.value;
	
	}
	else{
		assume offset >= 0;
		assume ThreadPool[tid].t_value_of_var[toRead.addr] > ThreadPool[tid].h_value_of_var[toRead.addr] ;
		assume ThreadPool[tid].wb_head < ThreadPool[tid].wb_tail;
		assume (toRead.dirty[tid]);
	
		result := toRead.valInbuffers[tid];

	}
	


}
procedure {:isatomic true} read(toRead:variable) returns(result : int ){

	if(*){
	//assume tid == recvThread || tid == senderThread;
		assume ThreadPool[tid].t_value_of_var[toRead.addr] == ThreadPool[tid].h_value_of_var[ toRead.addr] ;
		assume ThreadPool[tid].wb_head == ThreadPool[tid].wb_tail;
		assume (!toRead.dirty[tid]);
		
		result := toRead.value;
	
	}
	else{
	
		assume ThreadPool[tid].t_value_of_var[toRead.addr] > ThreadPool[tid].h_value_of_var[toRead.addr] ;
		assume ThreadPool[tid].wb_head < ThreadPool[tid].wb_tail;
		assume (toRead.dirty[tid]);
	
		result := toRead.valInbuffers[tid];

	}
}

const ownerThread :TID;
const unique T:variable;
const unique H:variable;
const unique tasks : variable;
const unique NULL :int ;



procedure pop1() returns (result: int)
{
  var local_tail: int;
  var local_tail_tmp:int ;
  var local_head: int;

    
    assume tid == ownerThread;

	call local_tail_tmp := read(T);
	local_tail := local_tail_tmp-1;
	call write(T,local_tail);
	call drain_last();

    atomic{  
		assert local_tail == T.value;
		call local_head := read(H);
		assume local_head < local_tail; // Propagated from below: THIS NEEDS ATTENTION, MAYBE NEW PROOF STEP.
	}		  

	atomic  {  
		assert local_tail == T.value;
		call result := read_from_ptr(tasks, local_tail);
        assume local_head < local_tail;
        return;
	}
}

procedure pop2() returns (result: int)
{
  var local_tail: int;
  var local_tail_tmp:int ;
  var local_head: int;


  assume tid == ownerThread;
  call local_tail_tmp := read(T);
  local_tail := local_tail_tmp -1 ;
  call write(T, local_tail);
  call drain_last();

  atomic  {
       assert local_tail == T.value;
		call result := read_from_ptr(tasks,local_tail);
  }

  atomic  {
     assert local_tail == T.value;
     // h := H; h_v := H_v;
    call local_head := read(H);
	assume local_head == local_tail;
  }


  atomic  {
		
		 assume local_head == local_tail;
          
        // assume h_v == H_v; assume h == H;
       assert local_tail == T.value;
	   call write(T, local_head + 1);
		call drain_last();
	   }

  atomic  {  
  	  
      //assert t_v == T_v;
      //assert t == T; Bu neden kapandi ????? Ask Serdar ?
	  assume local_head == H.value ;
	  call write(H,local_head+1);
	  call drain_last();
      return;
  }
}


procedure pop3() returns (result: int){

  var local_tail: int;
  var local_tail_tmp:int ;
  var local_head: int;

  	assume tid == ownerThread;

	call local_tail_tmp := read(T);
	local_tail := local_tail_tmp -1 ;
	call write(T, local_tail);
	call drain_last();

  atomic  {  
          assert local_tail == T.value;
          call local_head := read(H);
          assume local_tail < local_head; 
  }


  atomic  {  
  	  
	 assert local_tail == T.value;
  	 assert local_tail < local_head;
	 call write(T,local_head);
  	 call drain_last();
  }

  atomic  {
          result := NULL;
  }

}


procedure steal_succ() returns (result: int)
{
  var local_tail: int;
  var local_head: int;
  var tsk : int;

    

	    assume tid != ownerThread;
		call local_head := read(H);
		call tsk := read_from_ptr(tasks, local_head);   //
		
		
		call local_head :=  read( H); 
		assume local_head < T.value; 
		call tsk := read_from_ptr(tasks, local_head); 
			
            
	

    atomic{ // Update H as long as it H is not changed
         assume tid != ownerThread;
	    
		 call write(H,local_head + 1);
         call drain_last();
		 
    }

    result := tsk;
}

procedure steal_abort() returns (result: int){

  var local_tail: int;
  var local_head: int;

  //havoc h; // abstracted from h := H;
  //havoc t; // abstracted from t := T;
  // skip; // abstracted from assume h >= t;
  call local_tail := read(T);
  call local_head := read(H);
  assume local_head >= local_tail;
  result := NULL;
}


procedure put(x:int)
{
	var tail_index:int;
  
	assume ownerThread == tid ;
	
	call tail_index := read(T);
  	
	call write_to_ptr(tasks,tail_index, x);
	call drain_last();//ref_to_variable[x.addr].value[NEXT_PTR] := tAdr;
	
	call write(T,tail_index + 1);
	call drain_last();
}
