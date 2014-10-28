
invariant (forall t:thread, i:int :: t.h_value_of_var[i]<=t.t_value_of_var[i]);
invariant (forall t:thread :: t.wb_tail >= t.wb_head);
invariant (forall idx:int , t:thread :: idx >= t.wb_head && idx< t.wb_tail ==> t.h_value_of_var[t.wb[idx].addr]  < t.t_value_of_var[t.wb[idx].addr]);

invariant (forall t:TID , v:variable, i:int  :: 
  (i >= ThreadPool[t].h_value_of_var[v.value[ADDR]] &&  i < ThreadPool[t].t_value_of_var[v.value[ADDR]] /*&& v.dirty[tid]*/)  
	==>
  (ThreadPool[t].indx_of_var[v.value[ADDR],i] >= ThreadPool[t].wb_head && ThreadPool[t].indx_of_var[v.value[ADDR],i] < ThreadPool[t].wb_tail ));
	
invariant (forall t1,t2:TID :: ThreadPool[t1] != ThreadPool[t2] <==> t1 != t2);


invariant (forall rf:ref :: rf.index_of_ptr >= 0);

type field ;

const unique ADDR :field ;
const unique VAL : field ;
const unique VERSION:field ;
const unique NEXT_PTR : field ;
const unique DIRTY: field ;
const  unique ALLOC : field ; // Allocation'i da VALUE ile erisilebilinir hale getir
const unique REC_VAL : field ;
const unique INDX_BUF : field ;



// Probably ADDR, VAL and NEXT_PTR is enough !!!
axiom (forall fld : field ::fld == ADDR ||
	fld == VAL ||
	fld == VERSION ||
	fld == NEXT_PTR ||
	fld == DIRTY ||
	fld == ALLOC ||
	fld == REC_VAL ||
	fld == INDX_BUF);


record ref{
	addr : int ;
	index_of_ptr:int;
}
 	
record variable{
	
	value:[field]int;// value of variable : holds any addr of any type.
	ver:int ; // global version number of a variable.
	//heapState:allocation;
	dirty:[TID,field]bool; // is there is any write in any of buffer for this variable then it is false
	valInbuffers:[TID,field]int ; // value of recent write in ThreadPool[tid]
	indxInbuffers:[TID]int; // index of recent value in ThreadPool[tid]
}


record assignment{
	addr:int;
	f_n:field;
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
var ref_to_variable:[int]variable;	
var var_to_reference:[int]ref;

procedure {:isatomic true} drain_last()
{
		
		
	var bastakiAdres:int ;
	var bastakiFieldNum:field;
	var bastakiValue : int;
	var dirtySet : bool;
	
	var ref_to_flush : ref;
	
	
	bastakiAdres := ThreadPool[tid].wb[ThreadPool[tid].wb_head].addr;
	bastakiFieldNum := ThreadPool[tid].wb[ThreadPool[tid].wb_head].f_n;
	bastakiValue := ThreadPool[tid].wb[ThreadPool[tid].wb_head].value;
	
	//ref_to_flush := var_to_reference[bastakiAdres];
	
	assert (ThreadPool[tid].t_value_of_var[bastakiAdres] == ThreadPool[tid].h_value_of_var[bastakiAdres] +1);
	assert ((ThreadPool[tid].wb_head + 1 ) == ThreadPool[tid].wb_tail);


	assert ref_to_variable[bastakiAdres].dirty[tid,bastakiFieldNum];
	assert 	ThreadPool[tid].indx_of_var[bastakiAdres,ThreadPool[tid].h_value_of_var[bastakiAdres]] == ThreadPool[tid].wb_head;
	assert	ThreadPool[tid].indx_of_var[bastakiAdres,ThreadPool[tid].t_value_of_var[bastakiAdres]] == ThreadPool[tid].wb_tail;	
	

	ref_to_variable[bastakiAdres].value[bastakiFieldNum] := 
		  ThreadPool[tid].value_of_var[bastakiAdres,ThreadPool[tid].h_value_of_var[bastakiAdres]];  
	
	
	// same addresses same variables ??
	assert ref_to_variable[bastakiAdres] == ref_to_variable[ThreadPool[tid].value_of_var[bastakiAdres,ThreadPool[tid].h_value_of_var[bastakiAdres]]];
	
	ref_to_variable[bastakiAdres].value[VERSION] := 
		ref_to_variable[bastakiAdres].value[VERSION] + 1;
	


	ref_to_variable[bastakiAdres].dirty[tid, bastakiFieldNum] := false;	

	// Violates		
	ThreadPool[tid].h_value_of_var[bastakiAdres] := ThreadPool[tid].h_value_of_var[bastakiAdres] + 1;
	ThreadPool[tid].wb_head := ThreadPool[tid].wb_head + 1;
			
	assert  ThreadPool[tid].h_value_of_var[bastakiAdres] == ThreadPool[tid].t_value_of_var[bastakiAdres]; 
	assert  !ref_to_variable[bastakiAdres].dirty[tid,bastakiFieldNum];
	assert 	ThreadPool[tid].wb_head == ThreadPool[tid].wb_tail;	
	assert false;			
}


procedure {:isatomic true} write(taddrR:ref, index_of_ref:int ,  sval:int, fld:field){

	var as:assignment;
	var oldH :int ;
	var oldT:int;
	var taddr : variable;
	//var sval : variable;
	var dirtySet:bool;
	
	taddr := ref_to_variable[taddrR.addr+index_of_ref];
	
	assert taddr.value[ADDR] == taddrR.addr+taddrR.index_of_ptr;
	assert ThreadPool[tid].wb_tail == ThreadPool[tid].wb_head ;
	
	assert ThreadPool[tid].t_value_of_var[taddr.value[ADDR]] == ThreadPool[tid].h_value_of_var[taddr.value[ADDR]];
	
	assert ThreadPool[tid].indx_of_var[taddr.value[ADDR], ThreadPool[tid].h_value_of_var[taddr.value[ADDR]]] == ThreadPool[tid].wb_head ;
	
	assert ThreadPool[tid].indx_of_var[taddr.value[ADDR], ThreadPool[tid].h_value_of_var[taddr.value[ADDR]]] == 
			ThreadPool[tid].indx_of_var[taddr.value[ADDR], ThreadPool[tid].t_value_of_var[taddr.value[ADDR]]];

	
 
	oldH := ThreadPool[tid].h_value_of_var[taddr.value[ADDR]];
	oldT := ThreadPool[tid].t_value_of_var[taddr.value[ADDR]];
	
	as.value := sval;
	as.addr := taddr.value[ADDR];
	as.f_n :=  fld;
	
	taddr.valInbuffers[tid,fld] :=  sval;
	taddr.dirty[tid,fld] := true;
	taddr.indxInbuffers[tid] := ThreadPool[tid].wb_tail;
	
	ThreadPool[tid].wb[ ThreadPool[tid].wb_tail] := as;
	
	ThreadPool[tid].value_of_var[taddr.value[ADDR],ThreadPool[tid].t_value_of_var[taddr.value[ADDR]]] := as.value;
	ThreadPool[tid].indx_of_var[taddr.value[ADDR],ThreadPool[tid].t_value_of_var[taddr.value[ADDR]]] := ThreadPool[tid].wb_tail;

	assert as.addr == taddr.value[ADDR];
	assert as.value == sval;
	assert ThreadPool[tid].t_value_of_var[as.addr] == ThreadPool[tid].h_value_of_var[as.addr];
	
	
	assert ThreadPool[tid].indx_of_var[taddr.value[ADDR],oldH] == ThreadPool[tid].wb_head ;	
	assert ThreadPool[tid].indx_of_var[taddr.value[ADDR],oldT] == ThreadPool[tid].wb_tail ;
	
	ThreadPool[tid].t_value_of_var[taddr.value[ADDR]] := ThreadPool[tid].t_value_of_var[taddr.value[ADDR]]+1;
	
	ThreadPool[tid].wb_tail := ThreadPool[tid].wb_tail + 1;
	
	assert false;
}

procedure {:isatomic true} read(toReadR:ref,index_of_pointer:int, fld:field) returns(result : int ){

	var toRead : variable;
	toRead := ref_to_variable[toReadR.addr+index_of_pointer];

		if(*){
			
			assume ThreadPool[tid].t_value_of_var[toRead.value[ADDR]] == ThreadPool[tid].h_value_of_var[ toRead.value[ADDR]] ;
			assume ThreadPool[tid].wb_head == ThreadPool[tid].wb_tail;
			assume (!toRead.dirty[tid,fld]);
		//	assume (!toReadR.fieldsMap[fld]);
			
			result := toRead.value[fld];
		
		}
		else{
		
			assume ThreadPool[tid].t_value_of_var[toRead.value[ADDR]] > ThreadPool[tid].h_value_of_var[toRead.value[ADDR]] ;
			assume ThreadPool[tid].wb_head < ThreadPool[tid].wb_tail;
			assume (toRead.dirty[tid,fld]);
			//assume (toReadR.fields[fld]);
		
			result := toRead.valInbuffers[tid,fld];

		}
}

const unique null: variable;
const unique EMPTY: int;
const ownerThread: 


var tasks:ref;
var H:ref;
var T:ref;




procedure {:isatomic} CAS(oldVal:int, newVal: int )
returns (r: bool)
{
  r := (ref_to_variable[H.addr].value[VAL]== oldVal);
  
  if(r)
  {
    ref_to_variable[H.addr].value[VAL] := newVal;
  }
}




procedure take() returns(v:int){
	
	var local_tail:int;
	var local_head:int;
	
	var ret_task:int;
	var head_changed : bool;
	
	
	call local_tail := read(T,0,VAL);
	
	local_tail := local_tail -1 ;
	call write(T,0,local_tail,VAL);
	call drain_last();
	
	call local_head := read(H,0,VAL);
	
	if(local_tail < local_head){
	
		call write(T,0,local_head,VAL);
		call drain_last();
		v:=EMPTY;
		return;

	}
	
	call ret_task := read(tasks,local_tail,VAL);
	
	if(local_tail > local_head ){
		v:= ret_task;
		return;
	}
	
	call write(T,0,local_head+1,VAL);
	call drain_last();
	
	call head_changed := CAS(local_head , local_head+1);
	if(head_changed){
	
		v := ret_task;
		return;
	}

}



procedure steal()
returns(v:int)
{
	var head_index:int;
	var tail_index:int;
	
	var local_tail:int;
	var local_head:int;
	
	var ret_task:int;
	var head_changed : bool;
	
	
	call local_tail := read(T,0,VAL);
	call local_head := read(H,0,VAL);
	
	if(local_head >= local_tail){
		v:=EMPTY;
		
		return; }
		
	call ret_task := read(tasks, local_head,VAL);
	call head_changed := CAS(local_head, local_head+1);
	
	if(head_changed){
		v:=ret_task;
		return;
	}
}

procedure put(x:int)
{
  var tail_index:int;
  

	call tail_index := read(T,0,VAL);
  	call write(tasks,tail_index, x,VAL);
	call drain_last();//ref_to_variable[x.addr].value[NEXT_PTR] := tAdr;
	call write(T,0,tail_index + 1, VAL);
	call drain_last();
}