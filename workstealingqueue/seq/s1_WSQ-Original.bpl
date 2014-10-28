
procedure {:isatomic} CAS(oldVal:int, newVal:int)
returns (r: bool)
{
  r := (H == oldVal);
  
  if(r)
  {
    H := newVal;
  }
}

const ownerThread :TID;
var T:int;
var H:int;
var tasks : [int]int;
const unique NULL :int ;
const unique EMPTY : int;
const unique ABORT : int ;

procedure pop() returns (result: int)
{
  var local_tail: int;
  var local_head: int;
  var ret_task:int;
  var head_not_changed : bool;
	
	local_tail := T-1;
	T := local_tail;
	
	local_head := H;
	
	if(local_tail < local_head){
	
		T := local_head;
		result := EMPTY;
		return;
	}
	ret_task := tasks[local_tail];
	
	if(local_tail > local_head){
		result:= ret_task;
		return;
	}
		
	
	
	call head_not_changed := CAS(local_head , local_head + 1);
	
	if(head_not_changed){
		T := local_head + 1;
		result:= ret_task;
		return;
	}
	else{
	
		result:=EMPTY;
		return;
	}
	
  	
}


procedure steal() returns (result: int)
{
  var local_tail: int;
  var local_head: int;
  var ret_task: int;
	var head_not_changed : bool ;

  
  
  
	local_head := H;
	local_tail := T;
	
	if(local_head >= local_tail){
		result:= EMPTY;
		return;
	}	
  
	ret_task := tasks[local_head];
	call head_not_changed := CAS(local_head , local_head + 1);
	
	
	if(head_not_changed){
	
		result := ret_task;
		return;
	}
	else{
		result := ABORT;
		return;	
	}
    
}


procedure put(x:int)
{
	var local_tail : int ;
	var local_head : int ;
	
	local_tail := T;
	tasks[local_tail] := x;
	T:= local_tail+1;
}
