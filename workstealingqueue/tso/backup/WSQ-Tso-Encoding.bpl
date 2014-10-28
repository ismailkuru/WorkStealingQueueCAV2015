var tasks: [int]int;
var H: int;
var H_v: int;
var T: int;
var T_v: int;

// invariant H <= T-1;

const ownerThread: TID;
const unique NULL: int;


procedure stealNull() returns (result: int){
  var t: int;
  var h: int;
  havoc h; // abstracted from h := H;
  havoc t; // abstracted from t := T;
  // skip; // abstracted from assume h >= t;
  result := NULL;
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
            havoc h; havoc h_v; assume h_v <= H_v;
            havoc tsk;
            if (*) {
				assume h_v == H_v; 
				h := H;
				assume h<T;
				tsk := tasks[h]; 
			}
            else { assume h_v != H_v; }
			
		
	}

    atomic {
         assume tid != ownerThread;
         // assert H < T;
         assume (h_v == H_v);
         H := h+1;

         tmp_h_v := H_v;
         tmp_h_v := tmp_h_v + 1;
         H_v := tmp_h_v;
    }

    result := tsk;
}

procedure push(tsk: int)
{
    var t: int;
    var t_v: int;
    var tmp_t_v: int;

    atomic  {  
		assume tid == ownerThread;
        t := T;
        t_v := T_v;
    }

    atomic  { 
		assume tid == ownerThread;
        tasks[t] := tsk;
    }

    atomic  { 	
		assume tid == ownerThread;
        assert t == T;
        assert t_v == T_v;
        T := t + 1;
        
        tmp_t_v := T_v;
        tmp_t_v := tmp_t_v + 1;
        T_v := tmp_t_v;
    }
}

procedure pop1() returns (result: int)
{
  var t: int;
  var t_v: int;
  var h: int;

  atomic  {  
  	  assume tid == ownerThread;
	  t := T - 1;
          t_v := T_v;

	  T := t;
          t_v := t_v + 1;
          T_v := t_v;
  }

  atomic  {
  	  assume tid == ownerThread;
          assert t_v == T_v;
          assert t == T;
          h := H;
          assume h < t; // Propagated from below: THIS NEEDS ATTENTION, MAYBE NEW PROOF STEP.
  }

  atomic  {  
  	  assume tid == ownerThread;
          assert t_v == T_v;
          assert t == T;

	  result := tasks[t];

          assume h < t;
          return;
  }
}

procedure pop2() returns (result: int)
{
  var t: int;
  var t_v: int;
  var h_v: int;
  var tmp_h_v: int;
  var tmp_t_v: int;
  var h: int;

  atomic  {  
  	  assume tid == ownerThread;
	  t := T - 1;
          t_v := T_v;

	  T := t;
          t_v := t_v + 1;
          T_v := t_v;
  }

  

  atomic  {
  	  assume tid == ownerThread;
          assert t_v == T_v;
          assert t == T;
          // h := H; h_v := H_v;
          havoc h; havoc h_v; assume h_v <= H_v;
          if (*) { assume h_v == H_v; h := H; } 
          else { assume h_v != H_v;}
          assume h == t;
  }
atomic  {
		assume tid == ownerThread;
        assert t_v == T_v;
        assert t == T;
		result := tasks[t];
		assume h == t;
  }

  atomic  {  
  	  assume tid == ownerThread;
      assert t_v == T_v;
      assert t == T;
	  assume (h == H) && (h_v == H_v);
	  
	  
	  
	  h := h + 1;

	  assume h == t;
	  
	  tmp_h_v := H_v;
	  tmp_h_v := tmp_h_v + 1;
          H := h;
	  H_v := tmp_h_v;

			  T:= h;
	  
	    tmp_t_v := tmp_t_v + 1;
		T_v := tmp_t_v;
        T := h + 1;
		assume h == t;
		return;
  }
}

procedure pop3() returns (result: int){

  var t: int;
  var t_v: int;
  var h_v: int;
  var tmp_h_v: int;
  var tmp_t_v: int;
  var h: int;


  atomic  {  
  	  assume tid == ownerThread;
	  t := T - 1;
          t_v := T_v;

	  T := t;
          t_v := t_v + 1;
          T_v := t_v;
  }

  atomic  {  
  	  assume tid == ownerThread;
          assert t == T;
          h := H;
          assume t < h; 
  }


  atomic  {  
  	  assume tid == ownerThread;
          assert t == T;
          
	  T := h;

          t_v := T_v;
          t_v := t_v + 1;
          T_v := t_v;
		  
		  assume t < h;
  }

  atomic  {
			assume t < h;
          result := NULL;
  }

}

procedure pop4() returns (result: int)
{
  var t: int;
  var t_v: int;
  var h_v: int;
  var tmp_h_v: int;
  var tmp_t_v: int;
  var h: int;

  atomic  {  
  	  assume tid == ownerThread;
	  t := T - 1;
          t_v := T_v;

	  T := t;
          t_v := t_v + 1;
          T_v := t_v;
  }

  

  atomic  {
  	  assume tid == ownerThread;
          assert t_v == T_v;
          assert t == T;
          // h := H; h_v := H_v;
          havoc h; havoc h_v; assume h_v <= H_v;
          if (*) { assume h_v == H_v; h := H; } 
          else { assume h_v != H_v;}
          assume h == t;
  }
atomic  {
		assume tid == ownerThread;
        assert t_v == T_v;
        assert t == T;
		result := tasks[t];
		assume h == t;
  }

  atomic  {  
  	  assume tid == ownerThread;
      //assert t_v == T_v;
      //assert t == T;
	  assume (h != H) && (h_v != H_v);
	  
	  result := NULL;
	  assume h == t;
		
		return;
  }
}