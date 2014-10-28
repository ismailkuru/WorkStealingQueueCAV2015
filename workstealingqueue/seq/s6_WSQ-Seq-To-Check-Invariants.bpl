var tasks: [int]int;

var H: int;

var H_version: int;

var T: int;

var T_version: int;

var MAX_tail: int;

var MIN_head: int;

const ownerThread: TID;

const unique NULL: int;

const unique EMPTY: int;

const unique ABORT: int;


invariant MIN_head <= H; //Ornek: Program H == 2 diye baslasin. Bu invariant yuzunden MIN_head == 5'ten baslamasi mumkun degil.
invariant T <= MAX_tail; 

invariant (forall i : int :: H<=i && i< T ==> tasks[i] >0 );
//invariant (H<=T && MIN_head  < H && !(tasks[MIN_head] >0)) ==> (forall hl:int :: hl <H && hl>MIN_head ==> tasks[hl]>0);
//invariant (H<=T &&  MAX_tail>=T &&  !(tasks[MAX_tail] > 0)) ==> (forall bt:int :: bt>=T && bt<MAX_tail ==> tasks[bt] > 0);

procedure steal_head_ge_tail() returns (result: int);



implementation steal_head_ge_tail() returns (result: int)
{
  var local_tail: int;
  var local_head: int;
  var ex: Exception;

 
    atomic  {  // Non-mover
        havoc local_head;
        havoc local_tail;
        result := EMPTY;
    }
}



procedure steal_head_ls_tail_succ_not() returns (result: int);



implementation steal_head_ls_tail_succ_not() returns (result: int)
{
  var local_tail: int;
  var local_head: int;
  var ret_task: int;
  var tmp_head_version: int;
  var local_head_version: int;
  var ex: Exception;

    atomic  {  // Non-mover
        assume tid != ownerThread;
        havoc local_head;
        havoc local_head_version;
        assume local_head_version <= H_version;
        havoc ret_task;
        assume local_head_version == H_version ==> local_head < T && local_head == H && tasks[local_head] == ret_task;
        assume tid != ownerThread;
        assume local_head_version != H_version;
        result := ABORT;
    }
}



procedure steal_head_ls_tail_succ() returns (result: int);



implementation steal_head_ls_tail_succ() returns (result: int)
{
  var local_tail: int;
  var local_head: int;
  var ret_task: int;
  var tmp_head_version: int;
  var local_head_version: int;
  var ex: Exception;

    atomic  {  // Non-mover
        assume tid != ownerThread;
        havoc local_head;
        havoc local_head_version;
        assume local_head_version <= H_version;
        havoc ret_task;
        assume local_head_version == H_version ==> local_head == H && local_head < T && ret_task == tasks[local_head];
        assume tid != ownerThread;
        assume local_head_version == H_version;
        H := local_head + 1;
        if (*) {
           assume(H < MIN_head);
           MIN_head := H;
        } else {
           assume(!(H < MIN_head));
        }
        tmp_head_version := H_version;
        tmp_head_version := tmp_head_version + 1;
        H_version := tmp_head_version;
        result := ret_task;
        assert result > 0;
    }
}



procedure push(ret_task: int);



implementation push(ret_task: int)
{
  var local_tail: int;
  var local_head: int;
  var local_tail_version: int;
  var tmp_tail_version: int;
  var local_max_tail: int;
  var ex: Exception;

  
    atomic  {  // Non-mover
        assume ret_task > 0;
        assume tid == ownerThread;
        local_tail := T;
        local_tail_version := T_version;
        assume local_tail <= T;
        assume tid == ownerThread;
        tasks[local_tail] := ret_task;
        assume local_tail <= T;
        assume tid == ownerThread;
        /* assert local_tail <= T; [Discharged] */
        /* assert local_tail_version == T_version; [Discharged] */
        T := local_tail + 1;
        if (*) {
          assume (T > MAX_tail);
          MAX_tail := T;
        } else {
          assume ( !(T > MAX_tail));
        }
        tmp_tail_version := T_version;
        tmp_tail_version := tmp_tail_version + 1;
        T_version := tmp_tail_version;
    }
}



procedure pop_head_ls_tail() returns (result: int);



implementation pop_head_ls_tail() returns (result: int)
{
  var local_tail: int;
  var local_tail_version: int;
  var local_head: int;
  var ex: Exception;


    atomic  {  // Non-mover
        assume tid == ownerThread;
        local_tail := T - 1;
        local_tail_version := T_version;
        T := local_tail;
        if (*) {
          assume (T > MAX_tail);
          MAX_tail := T;
        } else {
          assume ( !(T > MAX_tail));
        }
        local_tail_version := local_tail_version + 1;
        T_version := local_tail_version;
        assume tid == ownerThread;
        /* assert local_tail_version == T_version; [Discharged] */
        /* assert local_tail == T; [Discharged] */
        local_head := H;
        assume local_head < local_tail;
        assume tid == ownerThread;
        /* assert local_tail_version == T_version; [Discharged] */
        /* assert local_tail == T; [Discharged] */
        result := tasks[local_tail];
        assert result > 0;
        assume local_head < local_tail;
        return;
    }
}



procedure pop_head_eq_tail_suc() returns (result: int);



implementation pop_head_eq_tail_suc() returns (result: int)
{
  var local_tail: int;
  var local_tail_version: int;
  var local_head_version: int;
  var tmp_head_version: int;
  var tmp_tail_version: int;
  var local_head: int;
  var ex: Exception;


    atomic  {  // Non-mover
        assume tid == ownerThread;
        local_tail := T - 1;
        local_tail_version := T_version;
        T := local_tail;
        if (*) {
          assume (T > MAX_tail);
          MAX_tail := T;
        } else {
          assume ( !(T > MAX_tail));
        }
        local_tail_version := local_tail_version + 1;
        T_version := local_tail_version;
        assume tid == ownerThread;
        /* assert local_tail_version == T_version; [Discharged] */
        /* assert local_tail == T; [Discharged] */
        havoc local_head;
        havoc local_head_version;
        assume local_head_version <= H_version;
        assume local_head_version == H_version ==> local_head == H;
        assume local_head == local_tail;
        assume tid == ownerThread;
        /* assert local_tail_version == T_version; [Discharged] */
        /* assert local_tail == T; [Discharged] */
        result := tasks[local_tail];
        assume local_head == local_tail;
        assume tid == ownerThread;
        /* assert local_tail_version == T_version; [Discharged] */
        /* assert local_tail == T; [Discharged] */
        assume local_head == H && local_head_version == H_version;
        local_head := local_head + 1;
        assume local_head == local_tail;
        tmp_head_version := H_version;
        tmp_head_version := tmp_head_version + 1;
        H := local_head;
        if (*) {
           assume(H < MIN_head);
           MIN_head := H;
        } else {
           assume(!(H < MIN_head));
        }
        H_version := tmp_head_version;
        T := local_head;
        //if (*) {
        //  assume (T > MAX_tail);
        //  MAX_tail := T;
        //} else {
        //  assume ( !(T > MAX_tail));
        //}
        tmp_tail_version := tmp_tail_version + 1;
        T_version := tmp_tail_version;
        T := local_head + 1;
        if (*) {
          assume (T > MAX_tail);
          MAX_tail := T;
        } else {
          assume ( !(T > MAX_tail));
        }
        /* assert result > 0; [Discharged] */
        return;
    }
}



procedure pop_head_gt_tail() returns (result: int);



implementation pop_head_gt_tail() returns (result: int)
{
  var local_tail: int;
  var local_tail_version: int;
  var local_head_version: int;
  var tmp_head_version: int;
  var tmp_tail_version: int;
  var local_head: int;
  var ex: Exception;


    atomic  {  // Non-mover
        assume tid == ownerThread;
        local_tail := T - 1;
        local_tail_version := T_version;
        T := local_tail;
        //if (*) {
        //  assume (T > MAX_tail);
        //  MAX_tail := T;
        //} else {
        //  assume ( !(T > MAX_tail));
        //}
        local_tail_version := local_tail_version + 1;
        T_version := local_tail_version;
        assume tid == ownerThread;
        /* assert local_tail == T; [Discharged] */
        local_head := H;
        assume local_tail < local_head;
        assume tid == ownerThread;
        /* assert local_tail == T; [Discharged] */
        T := local_head;
        if (*) {
          assume (T > MAX_tail);
          MAX_tail := T;
        } else {
          assume ( !(T > MAX_tail));
        }
        local_tail_version := T_version;
        local_tail_version := local_tail_version + 1;
        T_version := local_tail_version;
        assume local_tail < local_head;
        assume tid == ownerThread;
        assume local_tail < local_head;
        result := EMPTY;
    }
}



procedure pop_head_eq_tail_not_succ() returns (result: int);



implementation pop_head_eq_tail_not_succ() returns (result: int)
{
  var local_tail: int;
  var local_tail_version: int;
  var local_head_version: int;
  var tmp_head_version: int;
  var tmp_tail_version: int;
  var local_head: int;
  var ex: Exception;


    atomic  {  // Non-mover
        assume tid == ownerThread;
        local_tail := T - 1;
        local_tail_version := T_version;
        T := local_tail;
        if (*) {
          assume (T > MAX_tail);
          MAX_tail := T;
        } else {
          assume ( !(T > MAX_tail));
        }
        local_tail_version := local_tail_version + 1;
        T_version := local_tail_version;
        assume tid == ownerThread;
        /* assert local_tail_version == T_version; [Discharged] */
        /* assert local_tail == T; [Discharged] */
        havoc local_head;
        havoc local_head_version;
        assume local_head_version <= H_version;
        assume local_head_version == H_version ==> local_head == H;
        assume local_head == local_tail;
        assume tid == ownerThread;
        /* assert local_tail_version == T_version; [Discharged] */
        /* assert local_tail == T; [Discharged] */
        result := tasks[local_tail];
        assume local_head == local_tail;
        assume tid == ownerThread;
        assume local_head != H && local_head_version != H_version;
        result := EMPTY;
        assume local_head == local_tail;
        return;
    }
}

