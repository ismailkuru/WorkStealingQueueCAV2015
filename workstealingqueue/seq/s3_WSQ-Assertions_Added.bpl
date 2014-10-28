

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
const unique ABORT : int;

procedure pop() returns (result : int ){

  var local_tail:int;
  var local_head:int;
  var ret_task:int;
  var head_changed:bool;


	local_tail := T-1;
	T := local_tail;
	
	local_head := H;
	
	if(*){ // local_tail < local_head
	
		assume local_tail < local_head;
		T := local_head;
		result := EMPTY;
		return;
	}
	else{
	
		assume local_tail >= local_head;
		ret_task := tasks[local_tail];
		if(*){		
			assume local_tail > local_head;
			assert ret_task > 0;
			result := ret_task;
			// no need
			assert result > 0;
			return;
		}
		else{
			assume local_tail == local_head;
			
			if(*){
			
				atomic{	assume local_head == H;	H:=local_head + 1;}
				T:= local_head + 1;
				assert ret_task > 0;
				result := ret_task;
			
				// no need;
				assert result > 0;
				return;
			
			}
			else{
			
				assume local_head != H;
				result := EMPTY;
				return;
			}
			
		}

	}
}


procedure steal() returns (result: int)
{

 	var local_tail: int;
	var local_head: int;
	var ret_task: int;

	local_head := H;
	local_tail := T;
	

	if(*){	 

	assume local_head >= local_tail;
		result := EMPTY;
		return;
	}			
	else{
		assume local_head < local_tail;
		ret_task := tasks[local_head];

			if(*){
				
				atomic{	
					assume local_head == H;
					H:= local_head +  1;
				}
				
				assert ret_task > 0;
				result:= ret_task;
				// no need 
				assert result > 0;
				return;
			}
			else{
			
				assume H != local_head ;
				result := ABORT;
				return;
			}
	}
	 
}



procedure put(tsk:int)
{
	var local_tail : int ;
	var local_head : int ;
	
	// put requires 
	assume tsk > 0;
	
	local_tail := T;
    tasks[local_tail] := tsk;
    T := local_tail + 1;
	
	// ensures that tasks[local_tail] >0
    assert tasks[local_tail] > 0;
}
