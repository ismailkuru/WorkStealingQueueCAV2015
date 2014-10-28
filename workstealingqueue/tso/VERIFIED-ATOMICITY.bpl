const ownerThread: TID;

const unique T: variable;

const unique H: variable;

const unique tasks: variable;

const unique NULL: int;

const unique ABORT: int;

procedure pop_head_ls_tail() returns (result: int);
  modifies variable_value, variable_ver, variable_dirty, thread_h_value_of_var, thread_wb_head, assignment_value, assignment_addr, variable_valInbuffers, variable_indxInbuffers, thread_wb, thread_value_of_var, thread_indx_of_var, thread_t_value_of_var, thread_wb_tail;



implementation pop_head_ls_tail() returns (result: int)
{
  var local_tail: int;
  var local_tail_tmp: int;
  var local_head: int;
  var ex: Exception;
  var fresh_0: int;
  var fresh_1: int;
  var fresh_2: int;
  var fresh_3: assignment;

  Atomic_1:
    atomic  {  // Non-mover
        assume tid == ownerThread;
        /* assert tid == ownerThread; [Discharged] */
        /* assert true; [Discharged] */
        /* call local_tail_tmp := read(T); */
        if (*)
        {
            assume ThreadPool[tid].t_value_of_var[T.addr] == ThreadPool[tid].h_value_of_var[T.addr];
            assume ThreadPool[tid].wb_head == ThreadPool[tid].wb_tail;
            assume !T.dirty[tid];
            local_tail_tmp := T.value;
        }
        else
        {
            assume ThreadPool[tid].t_value_of_var[T.addr] > ThreadPool[tid].h_value_of_var[T.addr];
            assume ThreadPool[tid].wb_head < ThreadPool[tid].wb_tail;
            assume T.dirty[tid];
            local_tail_tmp := T.valInbuffers[tid];
        }

        /* assert tid == ownerThread; [Discharged] */
        local_tail := local_tail_tmp - 1;
        /* assert tid == ownerThread; [Discharged] */
        /* assert true; [Discharged] */
        /* call write(T, local_tail); */
        assert ThreadPool[tid].wb_tail == ThreadPool[tid].wb_head;
        /* assert ThreadPool[tid].t_value_of_var[T.addr] == ThreadPool[tid].h_value_of_var[T.addr]; [Discharged] */
        assert ThreadPool[tid].indx_of_var[T.addr, ThreadPool[tid].h_value_of_var[T.addr]] == ThreadPool[tid].wb_head;
        /* assert ThreadPool[tid].indx_of_var[T.addr, ThreadPool[tid].h_value_of_var[T.addr]] == ThreadPool[tid].indx_of_var[T.addr, ThreadPool[tid].t_value_of_var[T.addr]]; [Discharged] */
        fresh_1 := ThreadPool[tid].h_value_of_var[T.addr];
        fresh_2 := ThreadPool[tid].t_value_of_var[T.addr];
        fresh_3.value := local_tail;
        fresh_3.addr := T.addr;
        T.valInbuffers[tid] := local_tail;
        T.dirty[tid] := true;
        T.indxInbuffers[tid] := ThreadPool[tid].wb_tail;
        ThreadPool[tid].wb[ThreadPool[tid].wb_tail] := fresh_3;
        ThreadPool[tid].value_of_var[T.addr, ThreadPool[tid].t_value_of_var[T.addr]] := fresh_3.value;
        ThreadPool[tid].indx_of_var[T.addr, ThreadPool[tid].t_value_of_var[T.addr]] := ThreadPool[tid].wb_tail;
        /* assert fresh_3.addr == T.addr; [Discharged] */
        /* assert fresh_3.value == local_tail; [Discharged] */
        /* assert ThreadPool[tid].t_value_of_var[fresh_3.addr] == ThreadPool[tid].h_value_of_var[fresh_3.addr]; [Discharged] */
        /* assert ThreadPool[tid].indx_of_var[T.addr, fresh_1] == ThreadPool[tid].wb_head; [Discharged] */
        /* assert ThreadPool[tid].indx_of_var[T.addr, fresh_2] == ThreadPool[tid].wb_tail; [Discharged] */
        ThreadPool[tid].t_value_of_var[T.addr] := ThreadPool[tid].t_value_of_var[T.addr] + 1;
        ThreadPool[tid].wb_tail := ThreadPool[tid].wb_tail + 1;
        assert false;
        /* assert tid == ownerThread; [Discharged] */
        /* assert true; [Discharged] */
        /* call drain_last(); */
        fresh_0 := ThreadPool[tid].wb[ThreadPool[tid].wb_head].addr;
        /* assert ThreadPool[tid].t_value_of_var[fresh_0] == ThreadPool[tid].h_value_of_var[fresh_0] + 1; [Discharged] */
        /* assert ThreadPool[tid].wb_head + 1 == ThreadPool[tid].wb_tail; [Discharged] */
        /* assert thread_local_to_variable[fresh_0].dirty[tid]; [Discharged] */
        /* assert ThreadPool[tid].indx_of_var[fresh_0, ThreadPool[tid].h_value_of_var[fresh_0]] == ThreadPool[tid].wb_head; [Discharged] */
        /* assert ThreadPool[tid].indx_of_var[fresh_0, ThreadPool[tid].t_value_of_var[fresh_0]] == ThreadPool[tid].wb_tail; [Discharged] */
        thread_local_to_variable[fresh_0].value := ThreadPool[tid].value_of_var[fresh_0, ThreadPool[tid].h_value_of_var[fresh_0]];
        thread_local_to_variable[fresh_0].ver := thread_local_to_variable[fresh_0].ver + 1;
        thread_local_to_variable[fresh_0].dirty[tid] := false;
        ThreadPool[tid].h_value_of_var[fresh_0] := ThreadPool[tid].h_value_of_var[fresh_0] + 1;
        ThreadPool[tid].wb_head := ThreadPool[tid].wb_head + 1;
        /* assert ThreadPool[tid].h_value_of_var[fresh_0] == ThreadPool[tid].t_value_of_var[fresh_0]; [Discharged] */
        /* assert !thread_local_to_variable[fresh_0].dirty[tid]; [Discharged] */
        /* assert ThreadPool[tid].wb_head == ThreadPool[tid].wb_tail; [Discharged] */
        /* assert false; [Discharged] */
        /* assert tid == ownerThread; [Discharged] */
        /* assert local_tail == T.value; [Discharged] */
        /* assert true; [Discharged] */
        /* call local_head := read(H); */
        if (*)
        {
            assume ThreadPool[tid].t_value_of_var[H.addr] == ThreadPool[tid].h_value_of_var[H.addr];
            assume ThreadPool[tid].wb_head == ThreadPool[tid].wb_tail;
            assume !H.dirty[tid];
            local_head := H.value;
        }
        else
        {
            assume ThreadPool[tid].t_value_of_var[H.addr] > ThreadPool[tid].h_value_of_var[H.addr];
            assume ThreadPool[tid].wb_head < ThreadPool[tid].wb_tail;
            assume H.dirty[tid];
            local_head := H.valInbuffers[tid];
        }

        assume local_head < local_tail;
        /* assert tid == ownerThread; [Discharged] */
        /* assert local_tail == T.value; [Discharged] */
        /* assert true; [Discharged] */
        /* call result := read_from_ptr(tasks, local_tail); */
        if (*)
        {
            assume local_tail >= 0;
            assume ThreadPool[tid].t_value_of_var[tasks.addr] == ThreadPool[tid].h_value_of_var[tasks.addr];
            assume ThreadPool[tid].wb_head == ThreadPool[tid].wb_tail;
            assume !tasks.dirty[tid];
            result := tasks.value;
        }
        else
        {
            assume local_tail >= 0;
            assume ThreadPool[tid].t_value_of_var[tasks.addr] > ThreadPool[tid].h_value_of_var[tasks.addr];
            assume ThreadPool[tid].wb_head < ThreadPool[tid].wb_tail;
            assume tasks.dirty[tid];
            result := tasks.valInbuffers[tid];
        }

        assume local_head < local_tail;
        return;
    }
}



procedure pop_head_eq_tail_suc() returns (result: int);
  modifies variable_value, variable_ver, variable_dirty, thread_h_value_of_var, thread_wb_head, assignment_value, assignment_addr, variable_valInbuffers, variable_indxInbuffers, thread_wb, thread_value_of_var, thread_indx_of_var, thread_t_value_of_var, thread_wb_tail;



implementation pop_head_eq_tail_suc() returns (result: int)
{
  var local_tail: int;
  var local_tail_tmp: int;
  var local_head: int;
  var ex: Exception;
  var fresh_0: int;
  var fresh_1: int;
  var fresh_2: int;
  var fresh_3: assignment;
  var fresh_4: int;
  var fresh_5: int;
  var fresh_6: assignment;
  var fresh_7: int;
  var fresh_8: int;
  var fresh_9: assignment;

  Atomic_19:
    atomic  {  // Non-mover
        assume tid == ownerThread;
        /* assert tid == ownerThread; [Discharged] */
        /* assert true; [Discharged] */
        /* call local_tail_tmp := read(T); */
        if (*)
        {
            assume ThreadPool[tid].t_value_of_var[T.addr] == ThreadPool[tid].h_value_of_var[T.addr];
            assume ThreadPool[tid].wb_head == ThreadPool[tid].wb_tail;
            assume !T.dirty[tid];
            local_tail_tmp := T.value;
        }
        else
        {
            assume ThreadPool[tid].t_value_of_var[T.addr] > ThreadPool[tid].h_value_of_var[T.addr];
            assume ThreadPool[tid].wb_head < ThreadPool[tid].wb_tail;
            assume T.dirty[tid];
            local_tail_tmp := T.valInbuffers[tid];
        }

        /* assert tid == ownerThread; [Discharged] */
        local_tail := local_tail_tmp - 1;
        /* assert tid == ownerThread; [Discharged] */
        /* assert true; [Discharged] */
        /* call write(T, local_tail); */
        assert ThreadPool[tid].wb_tail == ThreadPool[tid].wb_head;
        /* assert ThreadPool[tid].t_value_of_var[T.addr] == ThreadPool[tid].h_value_of_var[T.addr]; [Discharged] */
        assert ThreadPool[tid].indx_of_var[T.addr, ThreadPool[tid].h_value_of_var[T.addr]] == ThreadPool[tid].wb_head;
        /* assert ThreadPool[tid].indx_of_var[T.addr, ThreadPool[tid].h_value_of_var[T.addr]] == ThreadPool[tid].indx_of_var[T.addr, ThreadPool[tid].t_value_of_var[T.addr]]; [Discharged] */
        fresh_1 := ThreadPool[tid].h_value_of_var[T.addr];
        fresh_2 := ThreadPool[tid].t_value_of_var[T.addr];
        fresh_3.value := local_tail;
        fresh_3.addr := T.addr;
        T.valInbuffers[tid] := local_tail;
        T.dirty[tid] := true;
        T.indxInbuffers[tid] := ThreadPool[tid].wb_tail;
        ThreadPool[tid].wb[ThreadPool[tid].wb_tail] := fresh_3;
        ThreadPool[tid].value_of_var[T.addr, ThreadPool[tid].t_value_of_var[T.addr]] := fresh_3.value;
        ThreadPool[tid].indx_of_var[T.addr, ThreadPool[tid].t_value_of_var[T.addr]] := ThreadPool[tid].wb_tail;
        /* assert fresh_3.addr == T.addr; [Discharged] */
        /* assert fresh_3.value == local_tail; [Discharged] */
        /* assert ThreadPool[tid].t_value_of_var[fresh_3.addr] == ThreadPool[tid].h_value_of_var[fresh_3.addr]; [Discharged] */
        /* assert ThreadPool[tid].indx_of_var[T.addr, fresh_1] == ThreadPool[tid].wb_head; [Discharged] */
        /* assert ThreadPool[tid].indx_of_var[T.addr, fresh_2] == ThreadPool[tid].wb_tail; [Discharged] */
        ThreadPool[tid].t_value_of_var[T.addr] := ThreadPool[tid].t_value_of_var[T.addr] + 1;
        ThreadPool[tid].wb_tail := ThreadPool[tid].wb_tail + 1;
        assert false;
        /* assert tid == ownerThread; [Discharged] */
        /* assert true; [Discharged] */
        /* call drain_last(); */
        fresh_0 := ThreadPool[tid].wb[ThreadPool[tid].wb_head].addr;
        /* assert ThreadPool[tid].t_value_of_var[fresh_0] == ThreadPool[tid].h_value_of_var[fresh_0] + 1; [Discharged] */
        /* assert ThreadPool[tid].wb_head + 1 == ThreadPool[tid].wb_tail; [Discharged] */
        /* assert thread_local_to_variable[fresh_0].dirty[tid]; [Discharged] */
        /* assert ThreadPool[tid].indx_of_var[fresh_0, ThreadPool[tid].h_value_of_var[fresh_0]] == ThreadPool[tid].wb_head; [Discharged] */
        /* assert ThreadPool[tid].indx_of_var[fresh_0, ThreadPool[tid].t_value_of_var[fresh_0]] == ThreadPool[tid].wb_tail; [Discharged] */
        thread_local_to_variable[fresh_0].value := ThreadPool[tid].value_of_var[fresh_0, ThreadPool[tid].h_value_of_var[fresh_0]];
        thread_local_to_variable[fresh_0].ver := thread_local_to_variable[fresh_0].ver + 1;
        thread_local_to_variable[fresh_0].dirty[tid] := false;
        ThreadPool[tid].h_value_of_var[fresh_0] := ThreadPool[tid].h_value_of_var[fresh_0] + 1;
        ThreadPool[tid].wb_head := ThreadPool[tid].wb_head + 1;
        /* assert ThreadPool[tid].h_value_of_var[fresh_0] == ThreadPool[tid].t_value_of_var[fresh_0]; [Discharged] */
        /* assert !thread_local_to_variable[fresh_0].dirty[tid]; [Discharged] */
        /* assert ThreadPool[tid].wb_head == ThreadPool[tid].wb_tail; [Discharged] */
        /* assert false; [Discharged] */
        /* assert tid == ownerThread; [Discharged] */
        /* assert local_tail == T.value; [Discharged] */
        /* assert true; [Discharged] */
        /* call result := read_from_ptr(tasks, local_tail); */
        if (*)
        {
            assume local_tail >= 0;
            assume ThreadPool[tid].t_value_of_var[tasks.addr] == ThreadPool[tid].h_value_of_var[tasks.addr];
            assume ThreadPool[tid].wb_head == ThreadPool[tid].wb_tail;
            assume !tasks.dirty[tid];
            result := tasks.value;
        }
        else
        {
            assume local_tail >= 0;
            assume ThreadPool[tid].t_value_of_var[tasks.addr] > ThreadPool[tid].h_value_of_var[tasks.addr];
            assume ThreadPool[tid].wb_head < ThreadPool[tid].wb_tail;
            assume tasks.dirty[tid];
            result := tasks.valInbuffers[tid];
        }

        /* assert tid == ownerThread; [Discharged] */
        /* assert local_tail == T.value; [Discharged] */
        /* assert true; [Discharged] */
        /* call local_head := read(H); */
        if (*)
        {
            assume ThreadPool[tid].t_value_of_var[H.addr] == ThreadPool[tid].h_value_of_var[H.addr];
            assume ThreadPool[tid].wb_head == ThreadPool[tid].wb_tail;
            assume !H.dirty[tid];
            local_head := H.value;
        }
        else
        {
            assume ThreadPool[tid].t_value_of_var[H.addr] > ThreadPool[tid].h_value_of_var[H.addr];
            assume ThreadPool[tid].wb_head < ThreadPool[tid].wb_tail;
            assume H.dirty[tid];
            local_head := H.valInbuffers[tid];
        }

        assume local_head == local_tail;
        /* assert tid == ownerThread; [Discharged] */
        assume local_head == local_tail;
        /* assert local_tail == T.value; [Discharged] */
        /* assert true; [Discharged] */
        /* call write(T, local_head + 1); */
        /* assert ThreadPool[tid].wb_tail == ThreadPool[tid].wb_head; [Discharged] */
        /* assert ThreadPool[tid].t_value_of_var[T.addr] == ThreadPool[tid].h_value_of_var[T.addr]; [Discharged] */
        /* assert ThreadPool[tid].indx_of_var[T.addr, ThreadPool[tid].h_value_of_var[T.addr]] == ThreadPool[tid].wb_head; [Discharged] */
        /* assert ThreadPool[tid].indx_of_var[T.addr, ThreadPool[tid].h_value_of_var[T.addr]] == ThreadPool[tid].indx_of_var[T.addr, ThreadPool[tid].t_value_of_var[T.addr]]; [Discharged] */
        fresh_4 := ThreadPool[tid].h_value_of_var[T.addr];
        fresh_5 := ThreadPool[tid].t_value_of_var[T.addr];
        fresh_6.value := local_head + 1;
        fresh_6.addr := T.addr;
        T.valInbuffers[tid] := local_head + 1;
        T.dirty[tid] := true;
        T.indxInbuffers[tid] := ThreadPool[tid].wb_tail;
        ThreadPool[tid].wb[ThreadPool[tid].wb_tail] := fresh_6;
        ThreadPool[tid].value_of_var[T.addr, ThreadPool[tid].t_value_of_var[T.addr]] := fresh_6.value;
        ThreadPool[tid].indx_of_var[T.addr, ThreadPool[tid].t_value_of_var[T.addr]] := ThreadPool[tid].wb_tail;
        /* assert fresh_6.addr == T.addr; [Discharged] */
        /* assert fresh_6.value == local_head + 1; [Discharged] */
        /* assert ThreadPool[tid].t_value_of_var[fresh_6.addr] == ThreadPool[tid].h_value_of_var[fresh_6.addr]; [Discharged] */
        /* assert ThreadPool[tid].indx_of_var[T.addr, fresh_4] == ThreadPool[tid].wb_head; [Discharged] */
        /* assert ThreadPool[tid].indx_of_var[T.addr, fresh_5] == ThreadPool[tid].wb_tail; [Discharged] */
        ThreadPool[tid].t_value_of_var[T.addr] := ThreadPool[tid].t_value_of_var[T.addr] + 1;
        ThreadPool[tid].wb_tail := ThreadPool[tid].wb_tail + 1;
        /* assert false; [Discharged] */
        /* assert tid == ownerThread; [Discharged] */
        assume local_head == H.value;
        /* assert true; [Discharged] */
        /* call write(H, local_head + 1); */
        /* assert ThreadPool[tid].wb_tail == ThreadPool[tid].wb_head; [Discharged] */
        /* assert ThreadPool[tid].t_value_of_var[H.addr] == ThreadPool[tid].h_value_of_var[H.addr]; [Discharged] */
        /* assert ThreadPool[tid].indx_of_var[H.addr, ThreadPool[tid].h_value_of_var[H.addr]] == ThreadPool[tid].wb_head; [Discharged] */
        /* assert ThreadPool[tid].indx_of_var[H.addr, ThreadPool[tid].h_value_of_var[H.addr]] == ThreadPool[tid].indx_of_var[H.addr, ThreadPool[tid].t_value_of_var[H.addr]]; [Discharged] */
        fresh_7 := ThreadPool[tid].h_value_of_var[H.addr];
        fresh_8 := ThreadPool[tid].t_value_of_var[H.addr];
        fresh_9.value := local_head + 1;
        fresh_9.addr := H.addr;
        H.valInbuffers[tid] := local_head + 1;
        H.dirty[tid] := true;
        H.indxInbuffers[tid] := ThreadPool[tid].wb_tail;
        ThreadPool[tid].wb[ThreadPool[tid].wb_tail] := fresh_9;
        ThreadPool[tid].value_of_var[H.addr, ThreadPool[tid].t_value_of_var[H.addr]] := fresh_9.value;
        ThreadPool[tid].indx_of_var[H.addr, ThreadPool[tid].t_value_of_var[H.addr]] := ThreadPool[tid].wb_tail;
        /* assert fresh_9.addr == H.addr; [Discharged] */
        /* assert fresh_9.value == local_head + 1; [Discharged] */
        /* assert ThreadPool[tid].t_value_of_var[fresh_9.addr] == ThreadPool[tid].h_value_of_var[fresh_9.addr]; [Discharged] */
        /* assert ThreadPool[tid].indx_of_var[H.addr, fresh_7] == ThreadPool[tid].wb_head; [Discharged] */
        /* assert ThreadPool[tid].indx_of_var[H.addr, fresh_8] == ThreadPool[tid].wb_tail; [Discharged] */
        ThreadPool[tid].t_value_of_var[H.addr] := ThreadPool[tid].t_value_of_var[H.addr] + 1;
        ThreadPool[tid].wb_tail := ThreadPool[tid].wb_tail + 1;
        /* assert false; [Discharged] */
        return;
    }
}



procedure pop_head_eq_tail_not_suc() returns (result: int);
  modifies variable_value, variable_ver, variable_dirty, thread_h_value_of_var, thread_wb_head, assignment_value, assignment_addr, variable_valInbuffers, variable_indxInbuffers, thread_wb, thread_value_of_var, thread_indx_of_var, thread_t_value_of_var, thread_wb_tail;



implementation pop_head_eq_tail_not_suc() returns (result: int)
{
  var local_tail: int;
  var local_tail_tmp: int;
  var local_head: int;
  var ex: Exception;
  var fresh_0: int;
  var fresh_1: int;
  var fresh_2: int;
  var fresh_3: assignment;

  Atomic_45:
    atomic  {  // Non-mover
        assume tid == ownerThread;
        /* assert tid == ownerThread; [Discharged] */
        /* assert true; [Discharged] */
        /* call local_tail_tmp := read(T); */
        if (*)
        {
            assume ThreadPool[tid].t_value_of_var[T.addr] == ThreadPool[tid].h_value_of_var[T.addr];
            assume ThreadPool[tid].wb_head == ThreadPool[tid].wb_tail;
            assume !T.dirty[tid];
            local_tail_tmp := T.value;
        }
        else
        {
            assume ThreadPool[tid].t_value_of_var[T.addr] > ThreadPool[tid].h_value_of_var[T.addr];
            assume ThreadPool[tid].wb_head < ThreadPool[tid].wb_tail;
            assume T.dirty[tid];
            local_tail_tmp := T.valInbuffers[tid];
        }

        /* assert tid == ownerThread; [Discharged] */
        local_tail := local_tail_tmp - 1;
        /* assert tid == ownerThread; [Discharged] */
        /* assert true; [Discharged] */
        /* call write(T, local_tail); */
        assert ThreadPool[tid].wb_tail == ThreadPool[tid].wb_head;
        /* assert ThreadPool[tid].t_value_of_var[T.addr] == ThreadPool[tid].h_value_of_var[T.addr]; [Discharged] */
        assert ThreadPool[tid].indx_of_var[T.addr, ThreadPool[tid].h_value_of_var[T.addr]] == ThreadPool[tid].wb_head;
        /* assert ThreadPool[tid].indx_of_var[T.addr, ThreadPool[tid].h_value_of_var[T.addr]] == ThreadPool[tid].indx_of_var[T.addr, ThreadPool[tid].t_value_of_var[T.addr]]; [Discharged] */
        fresh_1 := ThreadPool[tid].h_value_of_var[T.addr];
        fresh_2 := ThreadPool[tid].t_value_of_var[T.addr];
        fresh_3.value := local_tail;
        fresh_3.addr := T.addr;
        T.valInbuffers[tid] := local_tail;
        T.dirty[tid] := true;
        T.indxInbuffers[tid] := ThreadPool[tid].wb_tail;
        ThreadPool[tid].wb[ThreadPool[tid].wb_tail] := fresh_3;
        ThreadPool[tid].value_of_var[T.addr, ThreadPool[tid].t_value_of_var[T.addr]] := fresh_3.value;
        ThreadPool[tid].indx_of_var[T.addr, ThreadPool[tid].t_value_of_var[T.addr]] := ThreadPool[tid].wb_tail;
        /* assert fresh_3.addr == T.addr; [Discharged] */
        /* assert fresh_3.value == local_tail; [Discharged] */
        /* assert ThreadPool[tid].t_value_of_var[fresh_3.addr] == ThreadPool[tid].h_value_of_var[fresh_3.addr]; [Discharged] */
        /* assert ThreadPool[tid].indx_of_var[T.addr, fresh_1] == ThreadPool[tid].wb_head; [Discharged] */
        /* assert ThreadPool[tid].indx_of_var[T.addr, fresh_2] == ThreadPool[tid].wb_tail; [Discharged] */
        ThreadPool[tid].t_value_of_var[T.addr] := ThreadPool[tid].t_value_of_var[T.addr] + 1;
        ThreadPool[tid].wb_tail := ThreadPool[tid].wb_tail + 1;
        assert false;
        /* assert tid == ownerThread; [Discharged] */
        /* assert true; [Discharged] */
        /* call drain_last(); */
        fresh_0 := ThreadPool[tid].wb[ThreadPool[tid].wb_head].addr;
        /* assert ThreadPool[tid].t_value_of_var[fresh_0] == ThreadPool[tid].h_value_of_var[fresh_0] + 1; [Discharged] */
        /* assert ThreadPool[tid].wb_head + 1 == ThreadPool[tid].wb_tail; [Discharged] */
        /* assert thread_local_to_variable[fresh_0].dirty[tid]; [Discharged] */
        /* assert ThreadPool[tid].indx_of_var[fresh_0, ThreadPool[tid].h_value_of_var[fresh_0]] == ThreadPool[tid].wb_head; [Discharged] */
        /* assert ThreadPool[tid].indx_of_var[fresh_0, ThreadPool[tid].t_value_of_var[fresh_0]] == ThreadPool[tid].wb_tail; [Discharged] */
        thread_local_to_variable[fresh_0].value := ThreadPool[tid].value_of_var[fresh_0, ThreadPool[tid].h_value_of_var[fresh_0]];
        thread_local_to_variable[fresh_0].ver := thread_local_to_variable[fresh_0].ver + 1;
        thread_local_to_variable[fresh_0].dirty[tid] := false;
        ThreadPool[tid].h_value_of_var[fresh_0] := ThreadPool[tid].h_value_of_var[fresh_0] + 1;
        ThreadPool[tid].wb_head := ThreadPool[tid].wb_head + 1;
        /* assert ThreadPool[tid].h_value_of_var[fresh_0] == ThreadPool[tid].t_value_of_var[fresh_0]; [Discharged] */
        /* assert !thread_local_to_variable[fresh_0].dirty[tid]; [Discharged] */
        /* assert ThreadPool[tid].wb_head == ThreadPool[tid].wb_tail; [Discharged] */
        /* assert false; [Discharged] */
        /* assert tid == ownerThread; [Discharged] */
        /* assert local_tail == T.value; [Discharged] */
        /* assert true; [Discharged] */
        /* call result := read_from_ptr(tasks, local_tail); */
        if (*)
        {
            assume local_tail >= 0;
            assume ThreadPool[tid].t_value_of_var[tasks.addr] == ThreadPool[tid].h_value_of_var[tasks.addr];
            assume ThreadPool[tid].wb_head == ThreadPool[tid].wb_tail;
            assume !tasks.dirty[tid];
            result := tasks.value;
        }
        else
        {
            assume local_tail >= 0;
            assume ThreadPool[tid].t_value_of_var[tasks.addr] > ThreadPool[tid].h_value_of_var[tasks.addr];
            assume ThreadPool[tid].wb_head < ThreadPool[tid].wb_tail;
            assume tasks.dirty[tid];
            result := tasks.valInbuffers[tid];
        }

        /* assert tid == ownerThread; [Discharged] */
        /* assert local_tail == T.value; [Discharged] */
        /* assert true; [Discharged] */
        /* call local_head := read(H); */
        if (*)
        {
            assume ThreadPool[tid].t_value_of_var[H.addr] == ThreadPool[tid].h_value_of_var[H.addr];
            assume ThreadPool[tid].wb_head == ThreadPool[tid].wb_tail;
            assume !H.dirty[tid];
            local_head := H.value;
        }
        else
        {
            assume ThreadPool[tid].t_value_of_var[H.addr] > ThreadPool[tid].h_value_of_var[H.addr];
            assume ThreadPool[tid].wb_head < ThreadPool[tid].wb_tail;
            assume H.dirty[tid];
            local_head := H.valInbuffers[tid];
        }

        assume local_head == local_tail;
        /* assert tid == ownerThread; [Discharged] */
        assume local_head != H.value;
        result := NULL;
        return;
    }
}



procedure pop_head_gt_tail() returns (result: int);
  modifies variable_value, variable_ver, variable_dirty, thread_h_value_of_var, thread_wb_head, assignment_value, assignment_addr, variable_valInbuffers, variable_indxInbuffers, thread_wb, thread_value_of_var, thread_indx_of_var, thread_t_value_of_var, thread_wb_tail;



implementation pop_head_gt_tail() returns (result: int)
{
  var local_tail: int;
  var local_tail_tmp: int;
  var local_head: int;
  var ex: Exception;
  var fresh_0: int;
  var fresh_1: int;
  var fresh_2: int;
  var fresh_3: assignment;
  var fresh_4: int;
  var fresh_5: int;
  var fresh_6: assignment;

  Atomic_62:
    atomic  {  // Non-mover
        assume tid == ownerThread;
        /* assert tid == ownerThread; [Discharged] */
        /* assert true; [Discharged] */
        /* call local_tail_tmp := read(T); */
        if (*)
        {
            assume ThreadPool[tid].t_value_of_var[T.addr] == ThreadPool[tid].h_value_of_var[T.addr];
            assume ThreadPool[tid].wb_head == ThreadPool[tid].wb_tail;
            assume !T.dirty[tid];
            local_tail_tmp := T.value;
        }
        else
        {
            assume ThreadPool[tid].t_value_of_var[T.addr] > ThreadPool[tid].h_value_of_var[T.addr];
            assume ThreadPool[tid].wb_head < ThreadPool[tid].wb_tail;
            assume T.dirty[tid];
            local_tail_tmp := T.valInbuffers[tid];
        }

        /* assert tid == ownerThread; [Discharged] */
        local_tail := local_tail_tmp - 1;
        /* assert tid == ownerThread; [Discharged] */
        /* assert true; [Discharged] */
        /* call write(T, local_tail); */
        assert ThreadPool[tid].wb_tail == ThreadPool[tid].wb_head;
        /* assert ThreadPool[tid].t_value_of_var[T.addr] == ThreadPool[tid].h_value_of_var[T.addr]; [Discharged] */
        assert ThreadPool[tid].indx_of_var[T.addr, ThreadPool[tid].h_value_of_var[T.addr]] == ThreadPool[tid].wb_head;
        /* assert ThreadPool[tid].indx_of_var[T.addr, ThreadPool[tid].h_value_of_var[T.addr]] == ThreadPool[tid].indx_of_var[T.addr, ThreadPool[tid].t_value_of_var[T.addr]]; [Discharged] */
        fresh_1 := ThreadPool[tid].h_value_of_var[T.addr];
        fresh_2 := ThreadPool[tid].t_value_of_var[T.addr];
        fresh_3.value := local_tail;
        fresh_3.addr := T.addr;
        T.valInbuffers[tid] := local_tail;
        T.dirty[tid] := true;
        T.indxInbuffers[tid] := ThreadPool[tid].wb_tail;
        ThreadPool[tid].wb[ThreadPool[tid].wb_tail] := fresh_3;
        ThreadPool[tid].value_of_var[T.addr, ThreadPool[tid].t_value_of_var[T.addr]] := fresh_3.value;
        ThreadPool[tid].indx_of_var[T.addr, ThreadPool[tid].t_value_of_var[T.addr]] := ThreadPool[tid].wb_tail;
        /* assert fresh_3.addr == T.addr; [Discharged] */
        /* assert fresh_3.value == local_tail; [Discharged] */
        /* assert ThreadPool[tid].t_value_of_var[fresh_3.addr] == ThreadPool[tid].h_value_of_var[fresh_3.addr]; [Discharged] */
        /* assert ThreadPool[tid].indx_of_var[T.addr, fresh_1] == ThreadPool[tid].wb_head; [Discharged] */
        /* assert ThreadPool[tid].indx_of_var[T.addr, fresh_2] == ThreadPool[tid].wb_tail; [Discharged] */
        ThreadPool[tid].t_value_of_var[T.addr] := ThreadPool[tid].t_value_of_var[T.addr] + 1;
        ThreadPool[tid].wb_tail := ThreadPool[tid].wb_tail + 1;
        assert false;
        /* assert tid == ownerThread; [Discharged] */
        /* assert true; [Discharged] */
        /* call drain_last(); */
        fresh_0 := ThreadPool[tid].wb[ThreadPool[tid].wb_head].addr;
        /* assert ThreadPool[tid].t_value_of_var[fresh_0] == ThreadPool[tid].h_value_of_var[fresh_0] + 1; [Discharged] */
        /* assert ThreadPool[tid].wb_head + 1 == ThreadPool[tid].wb_tail; [Discharged] */
        /* assert thread_local_to_variable[fresh_0].dirty[tid]; [Discharged] */
        /* assert ThreadPool[tid].indx_of_var[fresh_0, ThreadPool[tid].h_value_of_var[fresh_0]] == ThreadPool[tid].wb_head; [Discharged] */
        /* assert ThreadPool[tid].indx_of_var[fresh_0, ThreadPool[tid].t_value_of_var[fresh_0]] == ThreadPool[tid].wb_tail; [Discharged] */
        thread_local_to_variable[fresh_0].value := ThreadPool[tid].value_of_var[fresh_0, ThreadPool[tid].h_value_of_var[fresh_0]];
        thread_local_to_variable[fresh_0].ver := thread_local_to_variable[fresh_0].ver + 1;
        thread_local_to_variable[fresh_0].dirty[tid] := false;
        ThreadPool[tid].h_value_of_var[fresh_0] := ThreadPool[tid].h_value_of_var[fresh_0] + 1;
        ThreadPool[tid].wb_head := ThreadPool[tid].wb_head + 1;
        /* assert ThreadPool[tid].h_value_of_var[fresh_0] == ThreadPool[tid].t_value_of_var[fresh_0]; [Discharged] */
        /* assert !thread_local_to_variable[fresh_0].dirty[tid]; [Discharged] */
        /* assert ThreadPool[tid].wb_head == ThreadPool[tid].wb_tail; [Discharged] */
        /* assert false; [Discharged] */
        /* assert tid == ownerThread; [Discharged] */
        /* assert local_tail == T.value; [Discharged] */
        /* assert true; [Discharged] */
        /* call local_head := read(H); */
        if (*)
        {
            assume ThreadPool[tid].t_value_of_var[H.addr] == ThreadPool[tid].h_value_of_var[H.addr];
            assume ThreadPool[tid].wb_head == ThreadPool[tid].wb_tail;
            assume !H.dirty[tid];
            local_head := H.value;
        }
        else
        {
            assume ThreadPool[tid].t_value_of_var[H.addr] > ThreadPool[tid].h_value_of_var[H.addr];
            assume ThreadPool[tid].wb_head < ThreadPool[tid].wb_tail;
            assume H.dirty[tid];
            local_head := H.valInbuffers[tid];
        }

        assume local_tail < local_head;
        /* assert tid == ownerThread; [Discharged] */
        /* assert local_tail == T.value; [Discharged] */
        /* assert local_tail < local_head; [Discharged] */
        /* assert true; [Discharged] */
        /* call write(T, local_head); */
        /* assert ThreadPool[tid].wb_tail == ThreadPool[tid].wb_head; [Discharged] */
        /* assert ThreadPool[tid].t_value_of_var[T.addr] == ThreadPool[tid].h_value_of_var[T.addr]; [Discharged] */
        /* assert ThreadPool[tid].indx_of_var[T.addr, ThreadPool[tid].h_value_of_var[T.addr]] == ThreadPool[tid].wb_head; [Discharged] */
        /* assert ThreadPool[tid].indx_of_var[T.addr, ThreadPool[tid].h_value_of_var[T.addr]] == ThreadPool[tid].indx_of_var[T.addr, ThreadPool[tid].t_value_of_var[T.addr]]; [Discharged] */
        fresh_4 := ThreadPool[tid].h_value_of_var[T.addr];
        fresh_5 := ThreadPool[tid].t_value_of_var[T.addr];
        fresh_6.value := local_head;
        fresh_6.addr := T.addr;
        T.valInbuffers[tid] := local_head;
        T.dirty[tid] := true;
        T.indxInbuffers[tid] := ThreadPool[tid].wb_tail;
        ThreadPool[tid].wb[ThreadPool[tid].wb_tail] := fresh_6;
        ThreadPool[tid].value_of_var[T.addr, ThreadPool[tid].t_value_of_var[T.addr]] := fresh_6.value;
        ThreadPool[tid].indx_of_var[T.addr, ThreadPool[tid].t_value_of_var[T.addr]] := ThreadPool[tid].wb_tail;
        /* assert fresh_6.addr == T.addr; [Discharged] */
        /* assert fresh_6.value == local_head; [Discharged] */
        /* assert ThreadPool[tid].t_value_of_var[fresh_6.addr] == ThreadPool[tid].h_value_of_var[fresh_6.addr]; [Discharged] */
        /* assert ThreadPool[tid].indx_of_var[T.addr, fresh_4] == ThreadPool[tid].wb_head; [Discharged] */
        /* assert ThreadPool[tid].indx_of_var[T.addr, fresh_5] == ThreadPool[tid].wb_tail; [Discharged] */
        ThreadPool[tid].t_value_of_var[T.addr] := ThreadPool[tid].t_value_of_var[T.addr] + 1;
        ThreadPool[tid].wb_tail := ThreadPool[tid].wb_tail + 1;
        /* assert false; [Discharged] */
        /* assert tid == ownerThread; [Discharged] */
        result := NULL;
    }
}



procedure steal_head_ls_tail_succ() returns (result: int);
  modifies variable_value, variable_ver, variable_dirty, thread_h_value_of_var, thread_wb_head, assignment_value, assignment_addr, variable_valInbuffers, variable_indxInbuffers, thread_wb, thread_value_of_var, thread_indx_of_var, thread_t_value_of_var, thread_wb_tail;



implementation steal_head_ls_tail_succ() returns (result: int)
{
  var local_tail: int;
  var local_head: int;
  var tsk: int;
  var ex: Exception;
  var fresh_0: int;
  var fresh_1: int;
  var fresh_2: int;
  var fresh_3: assignment;

  Atomic_78:
    atomic  {  // Non-mover
        assume tid != ownerThread;
        /* assert tid != ownerThread; [Discharged] */
        /* assert true; [Discharged] */
        /* call local_head := read(H); */
        if (*)
        {
            assume ThreadPool[tid].t_value_of_var[H.addr] == ThreadPool[tid].h_value_of_var[H.addr];
            assume ThreadPool[tid].wb_head == ThreadPool[tid].wb_tail;
            assume !H.dirty[tid];
            local_head := H.value;
        }
        else
        {
            assume ThreadPool[tid].t_value_of_var[H.addr] > ThreadPool[tid].h_value_of_var[H.addr];
            assume ThreadPool[tid].wb_head < ThreadPool[tid].wb_tail;
            assume H.dirty[tid];
            local_head := H.valInbuffers[tid];
        }

        /* assert tid != ownerThread; [Discharged] */
        /* assert true; [Discharged] */
        /* call tsk := read_from_ptr(tasks, local_head); */
        if (*)
        {
            assume local_head >= 0;
            assume ThreadPool[tid].t_value_of_var[tasks.addr] == ThreadPool[tid].h_value_of_var[tasks.addr];
            assume ThreadPool[tid].wb_head == ThreadPool[tid].wb_tail;
            assume !tasks.dirty[tid];
            tsk := tasks.value;
        }
        else
        {
            assume local_head >= 0;
            assume ThreadPool[tid].t_value_of_var[tasks.addr] > ThreadPool[tid].h_value_of_var[tasks.addr];
            assume ThreadPool[tid].wb_head < ThreadPool[tid].wb_tail;
            assume tasks.dirty[tid];
            tsk := tasks.valInbuffers[tid];
        }

        /* assert tid != ownerThread; [Discharged] */
        assume tid != ownerThread;
        /* assert true; [Discharged] */
        /* call write(H, local_head + 1); */
        assert ThreadPool[tid].wb_tail == ThreadPool[tid].wb_head;
        /* assert ThreadPool[tid].t_value_of_var[H.addr] == ThreadPool[tid].h_value_of_var[H.addr]; [Discharged] */
        assert ThreadPool[tid].indx_of_var[H.addr, ThreadPool[tid].h_value_of_var[H.addr]] == ThreadPool[tid].wb_head;
        /* assert ThreadPool[tid].indx_of_var[H.addr, ThreadPool[tid].h_value_of_var[H.addr]] == ThreadPool[tid].indx_of_var[H.addr, ThreadPool[tid].t_value_of_var[H.addr]]; [Discharged] */
        fresh_1 := ThreadPool[tid].h_value_of_var[H.addr];
        fresh_2 := ThreadPool[tid].t_value_of_var[H.addr];
        fresh_3.value := local_head + 1;
        fresh_3.addr := H.addr;
        H.valInbuffers[tid] := local_head + 1;
        H.dirty[tid] := true;
        H.indxInbuffers[tid] := ThreadPool[tid].wb_tail;
        ThreadPool[tid].wb[ThreadPool[tid].wb_tail] := fresh_3;
        ThreadPool[tid].value_of_var[H.addr, ThreadPool[tid].t_value_of_var[H.addr]] := fresh_3.value;
        ThreadPool[tid].indx_of_var[H.addr, ThreadPool[tid].t_value_of_var[H.addr]] := ThreadPool[tid].wb_tail;
        /* assert fresh_3.addr == H.addr; [Discharged] */
        /* assert fresh_3.value == local_head + 1; [Discharged] */
        /* assert ThreadPool[tid].t_value_of_var[fresh_3.addr] == ThreadPool[tid].h_value_of_var[fresh_3.addr]; [Discharged] */
        /* assert ThreadPool[tid].indx_of_var[H.addr, fresh_1] == ThreadPool[tid].wb_head; [Discharged] */
        /* assert ThreadPool[tid].indx_of_var[H.addr, fresh_2] == ThreadPool[tid].wb_tail; [Discharged] */
        ThreadPool[tid].t_value_of_var[H.addr] := ThreadPool[tid].t_value_of_var[H.addr] + 1;
        ThreadPool[tid].wb_tail := ThreadPool[tid].wb_tail + 1;
        assert false;
        /* assert true; [Discharged] */
        /* call drain_last(); */
        fresh_0 := ThreadPool[tid].wb[ThreadPool[tid].wb_head].addr;
        /* assert ThreadPool[tid].t_value_of_var[fresh_0] == ThreadPool[tid].h_value_of_var[fresh_0] + 1; [Discharged] */
        /* assert ThreadPool[tid].wb_head + 1 == ThreadPool[tid].wb_tail; [Discharged] */
        /* assert thread_local_to_variable[fresh_0].dirty[tid]; [Discharged] */
        /* assert ThreadPool[tid].indx_of_var[fresh_0, ThreadPool[tid].h_value_of_var[fresh_0]] == ThreadPool[tid].wb_head; [Discharged] */
        /* assert ThreadPool[tid].indx_of_var[fresh_0, ThreadPool[tid].t_value_of_var[fresh_0]] == ThreadPool[tid].wb_tail; [Discharged] */
        thread_local_to_variable[fresh_0].value := ThreadPool[tid].value_of_var[fresh_0, ThreadPool[tid].h_value_of_var[fresh_0]];
        thread_local_to_variable[fresh_0].ver := thread_local_to_variable[fresh_0].ver + 1;
        thread_local_to_variable[fresh_0].dirty[tid] := false;
        ThreadPool[tid].h_value_of_var[fresh_0] := ThreadPool[tid].h_value_of_var[fresh_0] + 1;
        ThreadPool[tid].wb_head := ThreadPool[tid].wb_head + 1;
        /* assert ThreadPool[tid].h_value_of_var[fresh_0] == ThreadPool[tid].t_value_of_var[fresh_0]; [Discharged] */
        /* assert !thread_local_to_variable[fresh_0].dirty[tid]; [Discharged] */
        /* assert ThreadPool[tid].wb_head == ThreadPool[tid].wb_tail; [Discharged] */
        /* assert false; [Discharged] */
        /* assert tid != ownerThread; [Discharged] */
        result := tsk;
    }
}



procedure steal_head_ls_tail_succ_not() returns (result: int);



implementation steal_head_ls_tail_succ_not() returns (result: int)
{
  var local_tail: int;
  var local_head: int;
  var tsk: int;
  var ex: Exception;

  Atomic_87:
    atomic  {  // Non-mover
        assume tid != ownerThread;
        /* assert tid != ownerThread; [Discharged] */
        /* assert true; [Discharged] */
        /* call local_head := read(H); */
        if (*)
        {
            assume ThreadPool[tid].t_value_of_var[H.addr] == ThreadPool[tid].h_value_of_var[H.addr];
            assume ThreadPool[tid].wb_head == ThreadPool[tid].wb_tail;
            assume !H.dirty[tid];
            local_head := H.value;
        }
        else
        {
            assume ThreadPool[tid].t_value_of_var[H.addr] > ThreadPool[tid].h_value_of_var[H.addr];
            assume ThreadPool[tid].wb_head < ThreadPool[tid].wb_tail;
            assume H.dirty[tid];
            local_head := H.valInbuffers[tid];
        }

        /* assert tid != ownerThread; [Discharged] */
        /* assert true; [Discharged] */
        /* call tsk := read_from_ptr(tasks, local_head); */
        if (*)
        {
            assume local_head >= 0;
            assume ThreadPool[tid].t_value_of_var[tasks.addr] == ThreadPool[tid].h_value_of_var[tasks.addr];
            assume ThreadPool[tid].wb_head == ThreadPool[tid].wb_tail;
            assume !tasks.dirty[tid];
            tsk := tasks.value;
        }
        else
        {
            assume local_head >= 0;
            assume ThreadPool[tid].t_value_of_var[tasks.addr] > ThreadPool[tid].h_value_of_var[tasks.addr];
            assume ThreadPool[tid].wb_head < ThreadPool[tid].wb_tail;
            assume tasks.dirty[tid];
            tsk := tasks.valInbuffers[tid];
        }

        /* assert tid != ownerThread; [Discharged] */
        assume local_head != H.value;
        /* assert tid != ownerThread; [Discharged] */
        result := ABORT;
    }
}



procedure steal_head_ge_tail() returns (result: int);



implementation steal_head_ge_tail() returns (result: int)
{
  var local_tail: int;
  var local_head: int;
  var ex: Exception;

  Call_92:
    atomic  {  // Non-mover
        assert tid != ownerThread;
        /* assert true; [Discharged] */
        /* call local_tail := read(T); */
        if (*)
        {
            assume ThreadPool[tid].t_value_of_var[T.addr] == ThreadPool[tid].h_value_of_var[T.addr];
            assume ThreadPool[tid].wb_head == ThreadPool[tid].wb_tail;
            assume !T.dirty[tid];
            local_tail := T.value;
        }
        else
        {
            assume ThreadPool[tid].t_value_of_var[T.addr] > ThreadPool[tid].h_value_of_var[T.addr];
            assume ThreadPool[tid].wb_head < ThreadPool[tid].wb_tail;
            assume T.dirty[tid];
            local_tail := T.valInbuffers[tid];
        }

        /* assert tid != ownerThread; [Discharged] */
        /* assert true; [Discharged] */
        /* call local_head := read(H); */
        if (*)
        {
            assume ThreadPool[tid].t_value_of_var[H.addr] == ThreadPool[tid].h_value_of_var[H.addr];
            assume ThreadPool[tid].wb_head == ThreadPool[tid].wb_tail;
            assume !H.dirty[tid];
            local_head := H.value;
        }
        else
        {
            assume ThreadPool[tid].t_value_of_var[H.addr] > ThreadPool[tid].h_value_of_var[H.addr];
            assume ThreadPool[tid].wb_head < ThreadPool[tid].wb_tail;
            assume H.dirty[tid];
            local_head := H.valInbuffers[tid];
        }

        /* assert tid != ownerThread; [Discharged] */
        assume local_head >= local_tail;
        /* assert tid != ownerThread; [Discharged] */
        result := NULL;
    }
}



procedure put(x: int);
  modifies variable_value, variable_ver, variable_dirty, thread_h_value_of_var, thread_wb_head, assignment_value, assignment_addr, variable_valInbuffers, variable_indxInbuffers, thread_wb, thread_value_of_var, thread_indx_of_var, thread_t_value_of_var, thread_wb_tail;



implementation put(x: int)
{
  var tail_index: int;
  var ex: Exception;
  var fresh_0: int;
  var fresh_1: int;
  var fresh_2: int;
  var fresh_3: int;
  var fresh_4: int;
  var fresh_5: assignment;
  var fresh_6: int;
  var fresh_7: int;
  var fresh_8: assignment;

  Atomic_96:
    atomic  {  // Non-mover
        assume ownerThread == tid;
        /* assert tid == ownerThread; [Discharged] */
        /* assert true; [Discharged] */
        /* call tail_index := read(T); */
        if (*)
        {
            assume ThreadPool[tid].t_value_of_var[T.addr] == ThreadPool[tid].h_value_of_var[T.addr];
            assume ThreadPool[tid].wb_head == ThreadPool[tid].wb_tail;
            assume !T.dirty[tid];
            tail_index := T.value;
        }
        else
        {
            assume ThreadPool[tid].t_value_of_var[T.addr] > ThreadPool[tid].h_value_of_var[T.addr];
            assume ThreadPool[tid].wb_head < ThreadPool[tid].wb_tail;
            assume T.dirty[tid];
            tail_index := T.valInbuffers[tid];
        }

        /* assert tid == ownerThread; [Discharged] */
        /* assert true; [Discharged] */
        /* call write_to_ptr(tasks, tail_index, x); */
        assume tail_index >= 0;
        fresh_2 := tasks.addr + tail_index;
        assert ThreadPool[tid].wb_tail == ThreadPool[tid].wb_head;
        assert ThreadPool[tid].t_value_of_var[fresh_2] == ThreadPool[tid].h_value_of_var[fresh_2];
        assert ThreadPool[tid].indx_of_var[fresh_2, ThreadPool[tid].h_value_of_var[fresh_2]] == ThreadPool[tid].wb_head;
        /* assert ThreadPool[tid].indx_of_var[fresh_2, ThreadPool[tid].h_value_of_var[fresh_2]] == ThreadPool[tid].indx_of_var[fresh_2, ThreadPool[tid].t_value_of_var[fresh_2]]; [Discharged] */
        fresh_3 := ThreadPool[tid].h_value_of_var[fresh_2];
        fresh_4 := ThreadPool[tid].t_value_of_var[fresh_2];
        fresh_5.value := x;
        fresh_5.addr := fresh_2;
        thread_local_to_variable[fresh_2].valInbuffers[tid] := x;
        thread_local_to_variable[fresh_2].dirty[tid] := true;
        thread_local_to_variable[fresh_2].indxInbuffers[tid] := ThreadPool[tid].wb_tail;
        ThreadPool[tid].wb[ThreadPool[tid].wb_tail] := fresh_5;
        ThreadPool[tid].value_of_var[fresh_2, ThreadPool[tid].t_value_of_var[fresh_2]] := fresh_5.value;
        ThreadPool[tid].indx_of_var[fresh_2, ThreadPool[tid].t_value_of_var[fresh_2]] := ThreadPool[tid].wb_tail;
        /* assert fresh_5.addr == fresh_2; [Discharged] */
        /* assert fresh_5.value == x; [Discharged] */
        /* assert ThreadPool[tid].t_value_of_var[fresh_5.addr] == ThreadPool[tid].h_value_of_var[fresh_5.addr]; [Discharged] */
        /* assert ThreadPool[tid].indx_of_var[fresh_2, fresh_3] == ThreadPool[tid].wb_head; [Discharged] */
        /* assert ThreadPool[tid].indx_of_var[fresh_2, fresh_4] == ThreadPool[tid].wb_tail; [Discharged] */
        ThreadPool[tid].t_value_of_var[fresh_2] := ThreadPool[tid].t_value_of_var[fresh_2] + 1;
        ThreadPool[tid].wb_tail := ThreadPool[tid].wb_tail + 1;
        assert false;
        /* assert tid == ownerThread; [Discharged] */
        /* assert true; [Discharged] */
        /* call drain_last(); */
        fresh_0 := ThreadPool[tid].wb[ThreadPool[tid].wb_head].addr;
        /* assert ThreadPool[tid].t_value_of_var[fresh_0] == ThreadPool[tid].h_value_of_var[fresh_0] + 1; [Discharged] */
        /* assert ThreadPool[tid].wb_head + 1 == ThreadPool[tid].wb_tail; [Discharged] */
        /* assert thread_local_to_variable[fresh_0].dirty[tid]; [Discharged] */
        /* assert ThreadPool[tid].indx_of_var[fresh_0, ThreadPool[tid].h_value_of_var[fresh_0]] == ThreadPool[tid].wb_head; [Discharged] */
        /* assert ThreadPool[tid].indx_of_var[fresh_0, ThreadPool[tid].t_value_of_var[fresh_0]] == ThreadPool[tid].wb_tail; [Discharged] */
        thread_local_to_variable[fresh_0].value := ThreadPool[tid].value_of_var[fresh_0, ThreadPool[tid].h_value_of_var[fresh_0]];
        thread_local_to_variable[fresh_0].ver := thread_local_to_variable[fresh_0].ver + 1;
        thread_local_to_variable[fresh_0].dirty[tid] := false;
        ThreadPool[tid].h_value_of_var[fresh_0] := ThreadPool[tid].h_value_of_var[fresh_0] + 1;
        ThreadPool[tid].wb_head := ThreadPool[tid].wb_head + 1;
        /* assert ThreadPool[tid].h_value_of_var[fresh_0] == ThreadPool[tid].t_value_of_var[fresh_0]; [Discharged] */
        /* assert !thread_local_to_variable[fresh_0].dirty[tid]; [Discharged] */
        /* assert ThreadPool[tid].wb_head == ThreadPool[tid].wb_tail; [Discharged] */
        /* assert false; [Discharged] */
        /* assert tid == ownerThread; [Discharged] */
        /* assert true; [Discharged] */
        /* call write(T, tail_index + 1); */
        /* assert ThreadPool[tid].wb_tail == ThreadPool[tid].wb_head; [Discharged] */
        /* assert ThreadPool[tid].t_value_of_var[T.addr] == ThreadPool[tid].h_value_of_var[T.addr]; [Discharged] */
        /* assert ThreadPool[tid].indx_of_var[T.addr, ThreadPool[tid].h_value_of_var[T.addr]] == ThreadPool[tid].wb_head; [Discharged] */
        /* assert ThreadPool[tid].indx_of_var[T.addr, ThreadPool[tid].h_value_of_var[T.addr]] == ThreadPool[tid].indx_of_var[T.addr, ThreadPool[tid].t_value_of_var[T.addr]]; [Discharged] */
        fresh_6 := ThreadPool[tid].h_value_of_var[T.addr];
        fresh_7 := ThreadPool[tid].t_value_of_var[T.addr];
        fresh_8.value := tail_index + 1;
        fresh_8.addr := T.addr;
        T.valInbuffers[tid] := tail_index + 1;
        T.dirty[tid] := true;
        T.indxInbuffers[tid] := ThreadPool[tid].wb_tail;
        ThreadPool[tid].wb[ThreadPool[tid].wb_tail] := fresh_8;
        ThreadPool[tid].value_of_var[T.addr, ThreadPool[tid].t_value_of_var[T.addr]] := fresh_8.value;
        ThreadPool[tid].indx_of_var[T.addr, ThreadPool[tid].t_value_of_var[T.addr]] := ThreadPool[tid].wb_tail;
        /* assert fresh_8.addr == T.addr; [Discharged] */
        /* assert fresh_8.value == tail_index + 1; [Discharged] */
        /* assert ThreadPool[tid].t_value_of_var[fresh_8.addr] == ThreadPool[tid].h_value_of_var[fresh_8.addr]; [Discharged] */
        /* assert ThreadPool[tid].indx_of_var[T.addr, fresh_6] == ThreadPool[tid].wb_head; [Discharged] */
        /* assert ThreadPool[tid].indx_of_var[T.addr, fresh_7] == ThreadPool[tid].wb_tail; [Discharged] */
        ThreadPool[tid].t_value_of_var[T.addr] := ThreadPool[tid].t_value_of_var[T.addr] + 1;
        ThreadPool[tid].wb_tail := ThreadPool[tid].wb_tail + 1;
        /* assert false; [Discharged] */
        /* assert tid == ownerThread; [Discharged] */
        /* assert true; [Discharged] */
        /* call drain_last(); */
        fresh_1 := ThreadPool[tid].wb[ThreadPool[tid].wb_head].addr;
        /* assert ThreadPool[tid].t_value_of_var[fresh_1] == ThreadPool[tid].h_value_of_var[fresh_1] + 1; [Discharged] */
        /* assert ThreadPool[tid].wb_head + 1 == ThreadPool[tid].wb_tail; [Discharged] */
        /* assert thread_local_to_variable[fresh_1].dirty[tid]; [Discharged] */
        /* assert ThreadPool[tid].indx_of_var[fresh_1, ThreadPool[tid].h_value_of_var[fresh_1]] == ThreadPool[tid].wb_head; [Discharged] */
        /* assert ThreadPool[tid].indx_of_var[fresh_1, ThreadPool[tid].t_value_of_var[fresh_1]] == ThreadPool[tid].wb_tail; [Discharged] */
        thread_local_to_variable[fresh_1].value := ThreadPool[tid].value_of_var[fresh_1, ThreadPool[tid].h_value_of_var[fresh_1]];
        thread_local_to_variable[fresh_1].ver := thread_local_to_variable[fresh_1].ver + 1;
        thread_local_to_variable[fresh_1].dirty[tid] := false;
        ThreadPool[tid].h_value_of_var[fresh_1] := ThreadPool[tid].h_value_of_var[fresh_1] + 1;
        ThreadPool[tid].wb_head := ThreadPool[tid].wb_head + 1;
        /* assert ThreadPool[tid].h_value_of_var[fresh_1] == ThreadPool[tid].t_value_of_var[fresh_1]; [Discharged] */
        /* assert !thread_local_to_variable[fresh_1].dirty[tid]; [Discharged] */
        /* assert ThreadPool[tid].wb_head == ThreadPool[tid].wb_tail; [Discharged] */
        /* assert false; [Discharged] */
    }
}



const MAX_INT: int;

const MIN_INT: int;

function ThreadLocal(TID) returns (bool);

axiom (forall t: TID :: { ThreadLocal(t) } ThreadLocal(t) <==> t == tid);

type AllocType;

const unique Alloc: AllocType;

const unique Dealloc: AllocType;

const unique Null: AllocType;

axiom (forall a: AllocType :: a == Alloc || a == Dealloc || a == Null);

function IsAlloc(AllocType) returns (bool);

axiom (forall a: AllocType :: { IsAlloc(a) } IsAlloc(a) <==> a == Alloc);

function IsDealloc(AllocType) returns (bool);

axiom (forall a: AllocType :: { IsDealloc(a) } IsDealloc(a) <==> a == Dealloc);

function IsNull(AllocType) returns (bool);

axiom (forall a: AllocType :: { IsNull(a) } IsNull(a) <==> a == Null);

record Mutex {
owner: TID;
alloc: AllocType;
}

type TID = int;

const unique tid: TID;

const unique tidx: TID;

axiom 0 < tid && 0 < tidx && tid != tidx;

const Tid: TID;

axiom 0 < Tid && tid <= Tid && tidx <= Tid;

record Thread {
id: TID;
interrupted: boolean;
alloc: AllocType;
owner: TID;
}

var Threads: [int]Thread;

const unique NULL_THREAD: Thread;

axiom IsNull(NULL_THREAD.alloc);

type Exception;

const unique ExReturn: Exception;

const unique ExSkip: Exception;

const unique ExBreak: Exception;

const unique ExContinue: Exception;

const unique NullPointerException: Exception;

const unique InterruptedException: Exception;

const unique Error: Exception;

const unique IllegalMonitorStateException: Exception;

const unique RuntimeException: Exception;

axiom subtype(NullPointerException, RuntimeException);

axiom subtype(IllegalMonitorStateException, RuntimeException);

function subtype(Exception, Exception) returns (bool);

axiom (forall e: Exception :: subtype(e, e));

axiom (forall e1: Exception, e2: Exception, e3: Exception :: { subtype(e1, e2), subtype(e2, e3) } subtype(e1, e2) && subtype(e2, e3) ==> subtype(e1, e3));

type boolean;

const unique True: boolean;

const unique False: boolean;

axiom (forall b: boolean :: b == True || b == False);

function toBool(boolean) returns (bool);

axiom (toBool(True) <==> true) && (toBool(False) <==> false);

function toBoolean(bool) returns (boolean);

axiom toBoolean(true) == True && toBoolean(false) == False;

type long = int;

function ReachBetween<T>(f: [T]T, x: T, y: T, z: T) returns (bool);

function ReachAvoiding<T>(f: [T]T, x: T, y: T, z: T) returns (bool);

function ReachBetweenSet<T>(f: [T]T, x: T, z: T) returns ([T]bool);

axiom (forall<T> f: [T]T, x: T, y: T, z: T :: { ReachBetweenSet(f, x, z)[y] } ReachBetweenSet(f, x, z)[y] <==> ReachBetween(f, x, y, z));

axiom (forall<T> f: [T]T, x: T, y: T, z: T :: { ReachBetween(f, x, y, z), ReachBetweenSet(f, x, z) } ReachBetween(f, x, y, z) ==> ReachBetweenSet(f, x, z)[y]);

axiom (forall<T> f: [T]T, x: T, z: T :: { ReachBetweenSet(f, x, z) } ReachBetween(f, x, x, x));

axiom (forall<T> f: [T]T, x: T :: ReachBetween(f, x, x, x));

axiom (forall<T> f: [T]T, x: T, y: T, z: T, w: T :: { ReachBetween(f, y, z, w), f[x] } ReachBetween(f, x, f[x], f[x]));

axiom (forall<T> f: [T]T, x: T, y: T :: { f[x], ReachBetween(f, x, y, y) } ReachBetween(f, x, y, y) ==> x == y || ReachBetween(f, x, f[x], y));

axiom (forall<T> f: [T]T, x: T, y: T :: { f[x], ReachBetween(f, x, y, y) } f[x] == x && ReachBetween(f, x, y, y) ==> x == y);

axiom (forall<T> f: [T]T, x: T, y: T :: { ReachBetween(f, x, y, x) } ReachBetween(f, x, y, x) ==> x == y);

axiom (forall<T> f: [T]T, x: T, y: T, z: T :: { ReachBetween(f, x, y, y), ReachBetween(f, x, z, z) } ReachBetween(f, x, y, y) && ReachBetween(f, x, z, z) ==> ReachBetween(f, x, y, z) || ReachBetween(f, x, z, y));

axiom (forall<T> f: [T]T, x: T, y: T, z: T :: { ReachBetween(f, x, y, z) } ReachBetween(f, x, y, z) ==> ReachBetween(f, x, y, y) && ReachBetween(f, y, z, z));

axiom (forall<T> f: [T]T, x: T, y: T, z: T :: { ReachBetween(f, x, y, y), ReachBetween(f, y, z, z) } ReachBetween(f, x, y, y) && ReachBetween(f, y, z, z) ==> ReachBetween(f, x, z, z));

axiom (forall<T> f: [T]T, x: T, y: T, z: T, w: T :: { ReachBetween(f, x, y, z), ReachBetween(f, y, w, z) } ReachBetween(f, x, y, z) && ReachBetween(f, y, w, z) ==> ReachBetween(f, x, y, w) && ReachBetween(f, x, w, z));

axiom (forall<T> f: [T]T, x: T, y: T, z: T, w: T :: { ReachBetween(f, x, y, z), ReachBetween(f, x, w, y) } ReachBetween(f, x, y, z) && ReachBetween(f, x, w, y) ==> ReachBetween(f, x, w, z) && ReachBetween(f, w, y, z));

axiom (forall<T> f: [T]T, u: T, x: T :: { ReachBetween(f, u, x, x) } ReachBetween(f, u, x, x) ==> ReachBetween(f, u, u, x));

axiom (forall<T> f: [T]T, x: T, y: T, z: T :: { ReachAvoiding(f, x, y, z) } { ReachBetween(f, x, y, z) } ReachAvoiding(f, x, y, z) <==> ReachBetween(f, x, y, z) || (ReachBetween(f, x, y, y) && !ReachBetween(f, x, z, z)));

axiom (forall<T> f: [T]T, u: T, v: T, x: T, p: T, q: T :: { ReachAvoiding(f[p := q], u, v, x) } ReachAvoiding(f[p := q], u, v, x) <==> (ReachAvoiding(f, u, v, p) && ReachAvoiding(f, u, v, x)) || (ReachAvoiding(f, u, p, x) && p != x && ReachAvoiding(f, q, v, p) && ReachAvoiding(f, q, v, x)));

function Equal<T>([T]bool, [T]bool) returns (bool);

function Subset<T>([T]bool, [T]bool) returns (bool);

function Disjoint<T>([T]bool, [T]bool) returns (bool);

function Empty<T>(T) returns ([T]bool);

function Singleton<T>(T) returns ([T]bool);

function Reachable<T>([T,T]bool, T) returns ([T]bool);

function Union<T>([T]bool, [T]bool) returns ([T]bool);

function Intersection<T>([T]bool, [T]bool) returns ([T]bool);

function Difference<T>([T]bool, [T]bool) returns ([T]bool);

function Dereference<T>([T]bool, [T]T) returns ([T]bool);

function Inverse<T>(f: [T]T, x: T) returns ([T]bool);

axiom (forall<T> x: T, y: T :: !Empty(y)[x]);

axiom (forall<T> x: T, y: T :: { Singleton(y)[x] } Singleton(y)[x] <==> x == y);

axiom (forall<T> y: T :: { Singleton(y) } Singleton(y)[y]);

axiom (forall<T> x: T, S: [T]bool, T: [T]bool :: { Union(S, T)[x] } Union(S, T)[x] <==> S[x] || T[x]);

axiom (forall<T> x: T, S: [T]bool, T: [T]bool :: { Union(S, T), S[x] } S[x] ==> Union(S, T)[x]);

axiom (forall<T> x: T, S: [T]bool, T: [T]bool :: { Union(S, T), T[x] } T[x] ==> Union(S, T)[x]);

axiom (forall<T> x: T, S: [T]bool, T: [T]bool :: { Intersection(S, T)[x] } Intersection(S, T)[x] <==> S[x] && T[x]);

axiom (forall<T> x: T, S: [T]bool, T: [T]bool :: { Intersection(S, T), S[x] } S[x] && T[x] ==> Intersection(S, T)[x]);

axiom (forall<T> x: T, S: [T]bool, T: [T]bool :: { Intersection(S, T), T[x] } S[x] && T[x] ==> Intersection(S, T)[x]);

axiom (forall<T> x: T, S: [T]bool, T: [T]bool :: { Difference(S, T)[x] } Difference(S, T)[x] <==> S[x] && !T[x]);

axiom (forall<T> x: T, S: [T]bool, T: [T]bool :: { Difference(S, T), S[x] } S[x] ==> Difference(S, T)[x] || T[x]);

axiom (forall<T> x: T, S: [T]bool, M: [T]T :: { Dereference(S, M)[x] } Dereference(S, M)[x] ==> (exists y: T :: x == M[y] && S[y]));

axiom (forall<T> x: T, S: [T]bool, M: [T]T :: { M[x], S[x], Dereference(S, M) } S[x] ==> Dereference(S, M)[M[x]]);

axiom (forall<T> x: T, y: T, S: [T]bool, M: [T]T :: { Dereference(S, M[x := y]) } !S[x] ==> Equal(Dereference(S, M[x := y]), Dereference(S, M)));

axiom (forall<T> x: T, y: T, S: [T]bool, M: [T]T :: { Dereference(S, M[x := y]) } S[x] && Equal(Intersection(Inverse(M, M[x]), S), Singleton(x)) ==> Equal(Dereference(S, M[x := y]), Union(Difference(Dereference(S, M), Singleton(M[x])), Singleton(y))));

axiom (forall<T> x: T, y: T, S: [T]bool, M: [T]T :: { Dereference(S, M[x := y]) } S[x] && !Equal(Intersection(Inverse(M, M[x]), S), Singleton(x)) ==> Equal(Dereference(S, M[x := y]), Union(Dereference(S, M), Singleton(y))));

axiom (forall<T> f: [T]T, x: T :: { Inverse(f, f[x]) } Inverse(f, f[x])[x]);

axiom (forall<T> f: [T]T, x: T, y: T :: { Inverse(f, y), f[x] } Inverse(f, y)[x] ==> f[x] == y);

axiom (forall<T> f: [T]T, x: T, y: T :: { Inverse(f[x := y], y) } Equal(Inverse(f[x := y], y), Union(Inverse(f, y), Singleton(x))));

axiom (forall<T> f: [T]T, x: T, y: T, z: T :: { Inverse(f[x := y], z) } y == z || Equal(Inverse(f[x := y], z), Difference(Inverse(f, z), Singleton(x))));

axiom (forall<T> S: [T]bool, T: [T]bool :: { Equal(S, T) } Equal(S, T) <==> Subset(S, T) && Subset(T, S));

axiom (forall<T> x: T, S: [T]bool, T: [T]bool :: { S[x], Subset(S, T) } S[x] && Subset(S, T) ==> T[x]);

axiom (forall<T> S: [T]bool, T: [T]bool :: { Subset(S, T) } Subset(S, T) || (exists x: T :: S[x] && !T[x]));

axiom (forall<T> x: T, S: [T]bool, T: [T]bool :: { S[x], Disjoint(S, T), T[x] } !(S[x] && Disjoint(S, T) && T[x]));

axiom (forall<T> S: [T]bool, T: [T]bool :: { Disjoint(S, T) } Disjoint(S, T) || (exists x: T :: S[x] && T[x]));

function Connected<T>(f: [T]T, x: T, y: T) returns (bool);

axiom (forall<T> f: [T]T, x: T, y: T :: { Connected(f, x, y) } Connected(f, x, y) <==> ReachBetween(f, x, y, y) || ReachBetween(f, y, x, x));

function Equals<T,K>([T]K, [T]K) returns (bool);

axiom (forall<T,K> A: [T]K, B: [T]K :: { Equals(A, B) } Equals(A, B) || (exists x: T :: A[x] != B[x]));

axiom (forall<T,K> A: [T]K, B: [T]K, x: T :: { Equals(A, B), A[x] } { Equals(A, B), B[x] } Equals(A, B) <==> A[x] == B[x]);

invariant (forall t: thread, i: int :: t.h_value_of_var[i] <= t.t_value_of_var[i]);

invariant (forall t: thread :: t.wb_tail >= t.wb_head);

invariant (forall idx: int, t: thread :: idx >= t.wb_head && idx < t.wb_tail ==> t.h_value_of_var[t.wb[idx].addr] < t.t_value_of_var[t.wb[idx].addr]);

invariant (forall t: TID, v: variable, i: int :: i >= ThreadPool[t].h_value_of_var[v.addr] && i < ThreadPool[t].t_value_of_var[v.addr] && v.dirty[tid] ==> ThreadPool[t].indx_of_var[v.addr, i] >= ThreadPool[t].wb_head && ThreadPool[t].indx_of_var[v.addr, i] < ThreadPool[t].wb_tail);

invariant (forall v1: variable, v2: variable :: v1 != v2 <==> v1.addr != v2.addr);

invariant (forall t1: TID, t2: TID :: ThreadPool[t1] != ThreadPool[t2] <==> t1 != t2);

record variable {
value: int;
addr: int;
ver: int;
dirty: [TID]bool;
allocation: bool;
valInbuffers: [TID]int;
indxInbuffers: [TID]int;
alloc: AllocType;
owner: TID;
}

record thread {
t_id: TID;
wb_head: int;
wb_tail: int;
wb: [int]assignment;
value_of_var: [int,int]int;
h_value_of_var: [int]int;
t_value_of_var: [int]int;
indx_of_var: [int,int]int;
alloc: AllocType;
owner: TID;
}

var ThreadPool: [TID]thread;

var thread_local_to_variable: [int]variable;

type field;

const unique ADDR: field;

const unique VAL: field;

const unique VERSION: field;

const unique NEXT_PTR: field;

const unique DIRTY: field;

const unique ALLOC: field;

const unique REC_VAL: field;

const unique INDX_BUF: field;

axiom (forall fld: field :: fld == ADDR || fld == VAL || fld == VERSION || fld == NEXT_PTR || fld == DIRTY || fld == ALLOC || fld == REC_VAL || fld == INDX_BUF);

record ref {
addr: int;
alloc: AllocType;
owner: TID;
}

record variable_heap {
value: [field]int;
ver: int;
dirty: [TID,field]bool;
valInbuffers: [TID,field]int;
indxInbuffers: [TID]int;
alloc: AllocType;
owner: TID;
}

record assignment {
addr: int;
f_n: field;
value: int;
alloc: AllocType;
owner: TID;
}

var ref_to_variable: [int]variable_heap;

function null_reference(referecen: ref) returns (bool);

axiom (forall refer: ref :: null_reference(refer) <==> refer.addr == null_heap_allocation.value[ADDR]);

const unique null_heap_allocation: variable_heap;

invariant (forall t: TID, v: variable, i: int :: i >= ThreadPool[t].h_value_of_var[v.addr] && i < ThreadPool[t].t_value_of_var[v.addr] && v.dirty[tid] ==> ThreadPool[t].indx_of_var[v.addr, i] >= ThreadPool[t].wb_head && ThreadPool[t].indx_of_var[v.addr, i] < ThreadPool[t].wb_tail);

invariant (forall t: thread, i: int :: t.h_value_of_var[i] <= t.t_value_of_var[i]);

invariant (forall v1: variable, v2: variable :: v1 != v2 <==> v1.addr != v2.addr);

invariant (forall t: thread :: t.wb_tail >= t.wb_head);

invariant (forall t1: TID, t2: TID :: ThreadPool[t1] != ThreadPool[t2] <==> t1 != t2);

invariant (forall idx: int, t: thread :: idx >= t.wb_head && idx < t.wb_tail ==> t.h_value_of_var[t.wb[idx].addr] < t.t_value_of_var[t.wb[idx].addr]);

