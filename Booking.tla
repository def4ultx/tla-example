----------------------------- MODULE Booking -----------------------------

EXTENDS Integers, Sequences, TLC, FiniteSets

NumHotel == 3
StartAllotment == 3
MaxAllotment == 3..3
\*CONSTANT MaxAllotment
MinPrice == 8
MaxPrice == 10

NumThreads == 2
Threads == 1..NumThreads

(*--algorithm booking
    variables 
        allotments \in [1..NumHotel -> {StartAllotment}];
        prices \in [1..NumHotel -> MaxPrice..MaxPrice];
        bookings \in [1..NumThreads -> { [request_price |-> 0, sell_price |-> 0] }];

define
\*    AllDone ==
\*            \A t \in 1..NumThreads: pc[t] = "Done"
\*            
\*    NoOverbook ==
\*        AllDone => \A x \in 1..NumHotel: allotments[x] >= 0
        
    
    NoOverbook ==
        \A x \in 1..NumHotel: allotments[x] >= 0
        
    NoBookingWithVariant ==
        \A x \in 1..NumThreads: bookings[x].request_price >= bookings[x].sell_price
        
    NoBookingWithNegativePriceDiff ==
        TRUE
\*        \A x \in 1..NumThreads: bookings[x].user >= bookings[x].system
        
end define;

process booking \in Threads
variables
    hotel \in 1..NumHotel;
    request_price = 0;
begin
    \* Search services
    GetPrice:
        request_price := prices[hotel];
        
    \* Booking services
    \* Architecture diagram
    CreateBooking:
        if allotments[hotel] > 0 then
            CheckPrice:
                if request_price >= prices[hotel] then
                    bookings[self] := [request_price |-> request_price, sell_price |-> prices[hotel]]; 
                    allotments[hotel] := allotments[hotel]-1;
                else
                    skip;
                end if;
        else
            skip;
        end if;
    
    Reset:
        goto GetPrice;
end process;

process supplier = 0
variables
    hotel \in 1..NumHotel;
begin   
    UpdateAvailability:
        either
            with update_price \in MinPrice..MaxPrice do
                prices[hotel] := update_price; 
            end with;
        or
            if allotments[hotel] < StartAllotment then
                allotments[hotel] := allotments[hotel]+1;
            else
                skip;
            end if;
        end either;
        goto UpdateAvailability;
end process;

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "979145b0" /\ chksum(tla) = "45bc11c9")
\* Process variable hotel of process booking at line 43 col 5 changed to hotel_
VARIABLES allotments, prices, bookings, pc

(* define statement *)
NoOverbook ==
    \A x \in 1..NumHotel: allotments[x] >= 0

NoBookingWithVariant ==
    \A x \in 1..NumThreads: bookings[x].request_price >= bookings[x].sell_price

NoBookingWithNegativePriceDiff ==
    TRUE

VARIABLES hotel_, request_price, hotel

vars == << allotments, prices, bookings, pc, hotel_, request_price, hotel >>

ProcSet == (Threads) \cup {0}

Init == (* Global variables *)
        /\ allotments \in [1..NumHotel -> {StartAllotment}]
        /\ prices \in [1..NumHotel -> MaxPrice..MaxPrice]
        /\ bookings \in [1..NumThreads -> { [request_price |-> 0, sell_price |-> 0] }]
        (* Process booking *)
        /\ hotel_ \in [Threads -> 1..NumHotel]
        /\ request_price = [self \in Threads |-> 0]
        (* Process supplier *)
        /\ hotel \in 1..NumHotel
        /\ pc = [self \in ProcSet |-> CASE self \in Threads -> "GetPrice"
                                        [] self = 0 -> "UpdateAvailability"]

GetPrice(self) == /\ pc[self] = "GetPrice"
                  /\ request_price' = [request_price EXCEPT ![self] = prices[hotel_[self]]]
                  /\ pc' = [pc EXCEPT ![self] = "CreateBooking"]
                  /\ UNCHANGED << allotments, prices, bookings, hotel_, hotel >>

CreateBooking(self) == /\ pc[self] = "CreateBooking"
                       /\ IF allotments[hotel_[self]] > 0
                             THEN /\ pc' = [pc EXCEPT ![self] = "CheckPrice"]
                             ELSE /\ TRUE
                                  /\ pc' = [pc EXCEPT ![self] = "Reset"]
                       /\ UNCHANGED << allotments, prices, bookings, hotel_, 
                                       request_price, hotel >>

CheckPrice(self) == /\ pc[self] = "CheckPrice"
                    /\ IF request_price[self] >= prices[hotel_[self]]
                          THEN /\ bookings' = [bookings EXCEPT ![self] = [request_price |-> request_price[self], sell_price |-> prices[hotel_[self]]]]
                               /\ allotments' = [allotments EXCEPT ![hotel_[self]] = allotments[hotel_[self]]-1]
                          ELSE /\ TRUE
                               /\ UNCHANGED << allotments, bookings >>
                    /\ pc' = [pc EXCEPT ![self] = "Reset"]
                    /\ UNCHANGED << prices, hotel_, request_price, hotel >>

Reset(self) == /\ pc[self] = "Reset"
               /\ pc' = [pc EXCEPT ![self] = "GetPrice"]
               /\ UNCHANGED << allotments, prices, bookings, hotel_, 
                               request_price, hotel >>

booking(self) == GetPrice(self) \/ CreateBooking(self) \/ CheckPrice(self)
                    \/ Reset(self)

UpdateAvailability == /\ pc[0] = "UpdateAvailability"
                      /\ \/ /\ \E update_price \in MinPrice..MaxPrice:
                                 prices' = [prices EXCEPT ![hotel] = update_price]
                            /\ UNCHANGED allotments
                         \/ /\ IF allotments[hotel] < StartAllotment
                                  THEN /\ allotments' = [allotments EXCEPT ![hotel] = allotments[hotel]+1]
                                  ELSE /\ TRUE
                                       /\ UNCHANGED allotments
                            /\ UNCHANGED prices
                      /\ pc' = [pc EXCEPT ![0] = "UpdateAvailability"]
                      /\ UNCHANGED << bookings, hotel_, request_price, hotel >>

supplier == UpdateAvailability

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == supplier
           \/ (\E self \in Threads: booking(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
