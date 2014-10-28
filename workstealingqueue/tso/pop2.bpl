procedure pop2() {


  var t: int;
  var t_v: int;
  var h_v: int;
  var tmp_h_v: int;
  var tmp_t_v: int;
  var h: int;
  var bi1:int;
  var bi2:int;

  atomic  {  
  	  assume tid == ownerThread;
          call t := read(T);
          t := t - 1;

          t_v := T_v;
          t_v := t_v + 1;

          call bi1 := write(T,t); // write returns the index of where in the write buffer t gotten 
          T_v := t_v;
  }

  // TSO yuzunden eklenen action
  // D1: Bu action'in "cinsi" D1 olsun. 
  // Asagida D1 cinsi actionlar yeniden gorunecek.
  atomic {
          assume tid == ownerThread;
          if (*) isAtHeadAndDrain(bi1); // Ek assertion yazmaya gerek yok mover yapmak icin.
                                        // bi1 drain edilirse T'ye yazilacak. Ama T'ye sadece ownerthread
                                        // yaziyor. Bu da birak assertion'i, assumption olarak var bu 
                                        // action'da.
  } 

  atomic  {
  	  assume tid == ownerThread;
          assert t_v == T_v;
          assert t == T;
	  call result := read_from_ptr(tasks, t);
  }

  // TSO yuzunden eklenen bir action daha.
  // D1: Bu action'in type'i D1, yukarida dedigim gibi. 
  atomic {
          assume tid == ownerThread;
          if (*) isAtHeadAndDrain(bi1); 
  }

  atomic  {
  	  assume tid == ownerThread;
          assert t_v == T_v;
          assert t == T;
          // h := H; h_v := H_v; // Normalde h'ye H'i okumak boyle oluyor ve h := read(H) yazmamiz lazim.
                                 // Asagida CAS oldugu icin boyle abstraction yapiyoruz. 
          havoc h; havoc h_v; assume h_v <= H_v;
          if (*) { assume h_v == H_v; h := H; } 
          else { assume h_v != H_v;}
          assume h == t;
  }

  // TSO yuzunden eklenen bir action daha.
  // D1: Bu action'in type'i D1, yukarida dedigim gibi. 
  atomic {
          assume tid == ownerThread;
          if (*) isAtHeadAndDrain(bi1); 
  }


  // Action #5
  atomic  {
  	  assume tid == ownerThread; 
          assume h == t; // (assm1) Bu bir label. Asagida kullanacagim bu label'i.     
          assert t_v == T_v; // (assrt1)
          // assume h_v == H_v; assume h == H;
          assert t == T; // (assrt2) 
	  
          // Increment T's version number
          tmp_t_v := T_v; 
          tmp_t_v := tmp_t_v + 1;
          T_v := tmp_t_v;
          // Bu write yerine asagidakini yaziyorum. T := h + 1;
          bi2 := write(T, h+1);
  }

  // Simdi "Gitmediyse once bi1, ardindan bi2" anlaminda yazacagiz.
  // D1: Bu action'in type'i D1, yukarida dedigim gibi. 
  atomic {
          assume h == t; // Yukaridaki assm1'i (local variable'lar cinsinden oldugu icin) buraya da yapistirdim
          assume tid == ownerThread;
          if (*) isAtHeadAndDrain(bi1); 
  }
  // D2: 
  atomic {
          assume h == t; // Yukaridaki assm1'i (local variable'lar cinsinden oldugu icin) buraya da yapistirdim
          assume tid == ownerThread;

          // Diyorum ki, eger bi2 buffer'in basindaysa, yukarida Action #5'te sozunu ettigim iki assertion
          // assrt1 ve assrt2 bu drain action'ina yapismis olsun.
          assert (bi2 == ThreadPool[tid].wb_head ==> 
                         t_v == T_v && // Bu (assrt1)
                         t == T) // Bu da (assrt2)
          if (*) isAtHeadAndDrain(bi2); 
  }

  atomic  {  
          // BU CAS action'i
          assume isBufferEmpty(ownerThread, threadPool);
  	  assume tid == ownerThread;
          //assert t_v == T_v;
          //assert t == T;
	  assume (h == H) && (h_v == H_v);
	  h := h + 1;
	  tmp_h_v := H_v;
	  tmp_h_v := tmp_h_v + 1;
          H := h; // Dogrudan memory'ye yaziyoruz, buffer'a degil
	  H_v := tmp_h_v;
          return;
  }

}