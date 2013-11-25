(*
  Programming Language Homework 3, ML programming
  copyright : Hongda Jiang
  date: Nov 11, 2013
  *)

signature ROOMDETAIL =
  sig
    val doubleAvailable : int
    val kingAvailable : int
    val queenAvailable : int
    val minnights : int option
  	val occupancyLimit : int
end;


functor MakeHotel (structure Q : ROOMDETAIL) :>
  sig
    datatype roomconfig = Dbed | Qbed | Kbed

	  type inventory

	  type resrecord = {uid: int, firstname: string, lastname: string, checkindate: int, 
			               nights: int, occupantsnum: int, config: roomconfig}
	  type ressys

	  exception NotEnoughRoom
	  exception UIDAlreadyExist
	  exception UIDNotExist
	  exception RestrictionsUnsatisfied
	  
	  val ifexist : int -> resrecord list -> bool
	  val empty :  ressys
	  val cancel :  ressys -> int -> ressys 
	  val getInventory :  ressys -> roomconfig -> int -> int
	  val getInventorySpan :  ressys -> roomconfig -> int -> int -> bool
	  val reserve :  ressys -> resrecord -> ressys 
	  val completedStays :  ressys -> int -> int
	  val removeCompletedStays : ressys -> int -> ressys 
	  val restrictions :  resrecord -> bool
	  val guestQuantity :  ressys -> int -> int


end = struct

	  open Q
    datatype roomconfig = Dbed | Qbed | Kbed

    type inventory = {dbed: int, qbed: int, kbed: int}

    type resrecord = {uid: int, firstname: string, lastname: string, checkindate: int, 
		                   nights: int, occupantsnum: int, config: roomconfig}

    type ressys = {rmquantities: inventory,  reservations: resrecord list}

     
    exception NotEnoughRoom
    exception UIDAlreadyExist
    exception UIDNotExist
    exception RestrictionsUnsatisfied

(*==========================  ifexist   =================================*)
(* This is a helper function to test if an uid is already in the records list
   In:  an uid , resrecord list
   Out: true if this uid is in the record list 
        false if not in the record list *)

    fun ifexist (id: int) [] = false
      | ifexist (id: int) ((r::rs): resrecord list) = 
                if (#uid r) = id then true
                else ifexist id rs

(*==========================  restrictions  =============================*)
(* This is a function to test if a reservation record is satisfied with the minNights and occupantsLimit restriciton
   In:  resrecord
   Out: true if this the record satisfy the restriction 
        false if doesn't *)

	fun restrictions (record: resrecord) = 
		let
			fun foo(NONE) = 0
			|   foo(SOME a) = a

		in
			if (#occupantsnum record) > Q.occupancyLimit then false
			else if (#nights record) < foo(Q.minnights) then false
            else true
		end
			
(*===============================  empty  ==================================*)
(* This is a function to evaluate to an empty reservation system
   In:  ---
   Out: a new reservation system without any reservation records*)

     val empty = 
	       let
            val quantity: inventory = {dbed = Q.doubleAvailable, qbed = Q.queenAvailable, kbed = Q.kingAvailable};
            val newsys: ressys = {rmquantities = quantity, reservations = []}
        in
	        newsys
        end  

(*==============================  cancel  =================================*)
(* This is a function to cancel a particular reservation record
   In:  an reservation record ,  an uid
   Out: an new reservation system with the particular record which has that uid removed  
        exception raised if such a record is not found*)

      fun cancel (oldsys: ressys) (id: int) =
           let
                val oldreservations: resrecord list = (#reservations oldsys);
                fun remove (idd: int)[] = []
                  | remove (idd: int)((r::rs): resrecord list) = 
                                           if (#uid r) = idd then rs
                                           else [r] @ (remove idd rs)
           in
              if ( ifexist id oldreservations )= false then raise UIDNotExist
              else {rmquantities = ((#rmquantities oldsys)), reservations = remove id oldreservations}
           end     

(*==============================  getInventory  ============================*)
(* This is a function to query the number of rooms available to be reserved for the specified configuration for the given date
   In:  an reservaton system, room config, date
   Out: the number of available rooms of this config on that day *)

      fun getInventory (sys: ressys) (rmconfig: roomconfig) (date: int) = 
          let  
              fun getquantity (iv: inventory)(rm: roomconfig) =
                  if rm = Dbed then (#dbed iv)
                  else if rm = Qbed then (#qbed iv)
                  else (#kbed iv)

              fun getReservedNum [] = 0
                | getReservedNum ((r::rs): resrecord list) =
                      if (#config r) = rmconfig andalso date >= (#checkindate r)  andalso  date < ((#checkindate r) + (#nights r))
                         then (1 + getReservedNum rs)
                      else (getReservedNum rs) 

          in
             getquantity (#rmquantities sys) rmconfig - getReservedNum (#reservations sys)
              
          end

(*==============================  getInventorySpan  =================================*)
(* This is a function to test if room inventory is available for all nights
   In:  an reservation system , room conofiguration, checkindate, staynights
   Out: true if room inventory is available for all nights
        false if not *)

       fun getInventorySpan (sys: ressys) (rmconfig: roomconfig) (date: int) (staynights: int) =
                if staynights <= 0 then true
                else if (getInventory sys rmconfig date) <= 0 then false
                else getInventorySpan sys rmconfig (date + 1) (staynights - 1)


(*==============================  reserve  ==========================================*)
(* This is a function to let user make a reservation
   In:  an reservation system ,  an reservation record
   Out: an new reservation system with the new record added 
   	    exception raised if this reservation doesn't satisfy the restriction of hotel, or the same uid already exists *)

       fun reserve (oldsys: ressys) (record: resrecord) =
               if (restrictions record) = false then raise RestrictionsUnsatisfied
               else if ( ifexist (#uid record) (#reservations oldsys) )= true then raise UIDAlreadyExist
               else if( getInventorySpan oldsys (#config record) (#checkindate record) (#nights record) ) = false then raise NotEnoughRoom
               else {rmquantities = #rmquantities oldsys, reservations = [record] @ (#reservations oldsys)}
              


(*==============================  completedStays  ====================================*)
(* This is a function to query the number of completed stays as of a particular date
   In:  an reservation system ,  date
   Out: the number of completed stays *)

       fun completedStays (sys: ressys) (date: int) = 
          let
              fun getStays [] = 0
                | getStays ((r::rs): resrecord list) =
                            if  (#checkindate r) + (#nights r) <= date  then  1 + getStays rs
                            else getStays rs
          in
              getStays (#reservations sys)
          end


(*==============================  removeCompletedStays  ====================================*)
(* This is a function remove all the completed stays before a particular date
   In:  an reservation system ,  date
   Out: an new reservation system with all the completed stays before that date removed *)

       fun removeCompletedStays (sys: ressys) (date: int) =
          let
              fun getNewRes [] = []
                | getNewRes ((r::rs): resrecord list) = 
                            if (#checkindate r) + (#nights r) <= date then getNewRes rs
                            else [r] @ getNewRes rs
              val newsys: ressys = {rmquantities = (#rmquantities sys), reservations = getNewRes (#reservations sys)}
          in
              newsys
          end

(*==============================  guestQuantity  ====================================*)
(* This is a function to query the number of gusets in hotel on a particular date
   In:  an reservation syste,  an date
   Out: the number of gusets in hotel on this date *)

       fun guestQuantity (sys: ressys) (date: int) = 
       		let
       			fun get [] = 0
       			|   get((r::rs): resrecord list) = 
       			    if (#checkindate r) <= date andalso (#checkindate r) + (#nights r) > date then 1 + get rs
       			    else get rs 
       		in
       			get (#reservations sys)
       		end
 end;









(*   ######################################## test code ###############################################  *)


(* ====================== Instantiate a structure adhering to the ROOMDETAIL signature =============== *)
structure MarriottRoomDetail:ROOMDETAIL = 
struct
      val doubleAvailable = 3
      val kingAvailable = 6
      val queenAvailable = 4
      val minnights = SOME 2
      val occupancyLimit = 4
end;

(*====================== Instantiate a hotel reservation structure using the functor =============== *)
  
structure MarriottHotelReservations = MakeHotel(structure Q = MarriottRoomDetail);

open MarriottHotelReservations;
val sys = empty;

(* ====================== Instantiate a hotel reservation structure using the functor =============== *)

val record1 = {uid = 1, firstname = "Hongda", lastname = "Jiang", checkindate = 1, nights = 3, occupantsnum = 2, config = Dbed};
val record2 = {uid = 2, firstname = "Hongda", lastname = "Jiang", checkindate = 2, nights = 4, occupantsnum = 2, config = Dbed};
val record3 = {uid = 3, firstname = "Hongda", lastname = "Jiang", checkindate = 3, nights = 5, occupantsnum = 2, config = Dbed};
val record4 = {uid = 4, firstname = "Hongda", lastname = "Jiang", checkindate = 4, nights = 8, occupantsnum = 2, config = Qbed};
val record5 = {uid = 5, firstname = "Hongda", lastname = "Jiang", checkindate = 4, nights = 7, occupantsnum = 2, config = Kbed};

val sys = reserve sys record1;
val sys = reserve sys record2;
val sys = reserve sys record3;
val sys = reserve sys record4;
val sys = reserve sys record5;


(* ====================== unsuccessful creation of a reservation due to lack of inventory =============== *)

val record6 = {uid = 6, firstname = "Hongda", lastname = "Jiang", checkindate = 2, nights = 3, occupantsnum = 2, config = Dbed};
val sys = reserve sys record6;

(* ======================= unsuccessful creation of a reservation due to Ristriction ==================== *)

val record7 = {uid = 7, firstname = "Hongda", lastname = "Jiang", checkindate = 2, nights = 1, occupantsnum = 2, config = Kbed};
val sys = reserve sys record7;

(* ======================== Cancel at least 2 reservations ===================================== *)

val sys = cancel sys 1;
val sys = cancel sys 2;

(* ========================= Query the room inventory, Qbed , date 5 =========================== *)

getInventory sys Qbed 5;

(* ========================= Demonstrate completedStays and removeCompletedStays ===============  *)

completedStays sys 10;
val sys = removeCompletedStays sys 10;
completedStays sys 10;

(* ========================== Demonstrate the guestQuantity ===================================== *)
guestQuantity sys 9;


