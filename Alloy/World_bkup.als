//signatures of all main objects

abstract sig Bool{}
one sig True extends Bool{}
one sig False extends Bool{}

//simplified date signature
sig Date{
    val : one Int
}

sig Coordinate{
    lat : one Int,
    lon : one Int
}

abstract sig ChargeRate{}
one sig Slow extends ChargeRate{}
one sig Fast extends ChargeRate{}
one sig Rapid extends ChargeRate{}

abstract sig EnergyType{}
one sig Green extends EnergyType{}
one sig Carbon extends EnergyType{}
one sig Nuclear extends EnergyType{}


sig Email{
    val: one String,
    verified : one Bool
}

sig Card{  
    CardNumber: one String,
    CardHolder: one String,
    ExpiryDate: one Date,
    CVV: one String,
    verified : one Bool
}

sig User{
    username: one String,
    password: one String,
    email: one Email,
    paymentMethod: some Card
}

sig Reservation{
    time: one Date,
    startTime: one Int,
    endTime: one Int,
    chargeRate: one ChargeRate,
    user: one User,
    chargingStation: one ChargingStation
}

sig ChargingStation{
    location: one Coordinate,
    name: one String,
    isDiscounted: one Bool,
    energyCost: one Int,
    batteryLevel: one Int,
    batteryEnergyValue: one Int,
    chargingColumns: some ChargingColumn,
    supplier: one DSO
}

sig DSO{
    name: one String,
    energyCost: one Int,
    energyType: one EnergyType    
}

sig ChargingColumn{
    type: one ChargeRate,
    isFull: one Bool,
    sockets: some Socket,
}

sig CPO{
    name: one String,
    employees: some CPOEmployee,
    chargingStations: some ChargingStation
}

sig CPOEmployee{
    username: one String,
    password: one String,
    workPlace: one ChargingStation
}

sig Socket{
    occupied: one Bool,
}



//all users must have verified mail and payment method to make a reservation
fact {
    all r:Reservation | (r.user.email.verified in True and r.user.paymentMethod.verified in True)
}

//no two charging stations can be at the same location and all coordinates must be in at least one of the charging stations
fact{
    all disj c1,c2:ChargingStation | c1.location != c2.location
    all c:Coordinate | c in ChargingStation.location
}

//all mails must be in at least one user
fact{
    all e:Email | e in User.email
}

//all Cards must be in at least one user
fact{
    all c:Card | c in User.paymentMethod
}

//all Dates must be in at least one reservation or card
fact{
    all d:Date | d in Reservation.time or d in Card.ExpiryDate
}

//no date can exist without a reservation or a DebitCard
fact{
    all d:Date | (some r:Reservation | (r.time = d)) or (some r:Card | (r.ExpiryDate = d))
}

//each chargingColumn is always in one and only one chargingStation
fact{
    all c:ChargingColumn | no disj c1,c2:ChargingStation | c in c1.chargingColumns and c in c2.chargingColumns
    all c:ChargingColumn | c in ChargingStation.chargingColumns
}

//no two CPOEmployees can have the same username
fact{
    all disj e1,e2:CPOEmployee | e1.username != e2.username
}

//each employee must work for one and only one CPO
fact{
    all e:CPOEmployee | no disj c1,c2:CPO | e in c1.employees and e in c2.employees
    all e:CPOEmployee | e in CPO.employees
}

//if all charging stations sockets are occupied, the charging column is full
fact{
    all c:ChargingColumn |  (no s:Socket | s in c.sockets and s.occupied in False) iff c.isFull = True
}


//all sockets must belong to one and only one charging column
fact{
    all s:Socket | no disj c1,c2:ChargingColumn | s in c1.sockets and s in c2.sockets
    all s:Socket | s in ChargingColumn.sockets
}

//all startTime must be greater than endTime
fact{
    all r:Reservation | r.startTime < r.endTime
}

//a reservation can be made only if the charging station has a charging column of the required type 
fact{
    all r:Reservation | r.chargeRate in r.chargingStation.chargingColumns.type
}

//users mail and username must be unique
fact{
    all disj u1,u2:User | u1.email != u2.email or u1.username != u2.username
}

//Strings exist
fact{
    all s:String | s in "a"+"b"+"c"+"d"
}

//all CPOEmployees must work in a charging station that belongs to the CPO they work for
fact{
    all c:CPO | c.employees.workPlace in c.chargingStations
}

//all charging station must belong to one and only one CPO
fact{
    all c:ChargingStation | no disj c1,c2:CPO | c in c1.chargingStations and c in c2.chargingStations
    all c:ChargingStation | c in CPO.chargingStations
}

//assertion

assert Check_CC_Status{
    all c:ChargingColumn | c.isFull = False
    all s:Socket | s.occupied = True 
    #sockets > 0
}

//PREDICATES

//dynamic predicates

//add a new card to user
pred addCardToUser[u,u':User, c:Card]{
    u'.paymentMethod = u.paymentMethod + c
}

//add a new reservation
pred addReservation[r,r':Reservation, cr:ChargeRate, cs:ChargingStation, u:User,]{
    r'.chargeRate = cr
    r'.chargingStation = cs
    r != r'
}

//change DSO for a charging station
pred changeDSO[c:ChargingStation, d,d':DSO]{
    d != d' and 
    d.energyCost >= d'.energyCost and
    c.supplier = d'
}

//Charging station changes price
pred changePrice[c:ChargingStation, p,p':Int]{
    c.energyCost = p and
    p != p' 
}

//worlds
pred eMSPWorld{
    #ChargingStation = 0
    #DSO = 0
    #Reservation = 0
    #User = 2
    #Card = 3
    #Email = 1
}

pred CPMSWorld{
    #ChargingStation = 2
    #DSO = 2
    #Reservation = 0
    #CPO = 2
    #CPOEmployee = 3
    #Socket = 6
}

pred World{
    #Reservation = 2
    #User = 2
    #Card = 1
    #Email = 2
    #ChargingStation = 2
    #ChargingColumn = 2
    #Socket = 3
    #DSO = 1
}

//run

run {
    
    //#Reservation = 1 
}

run eMSPWorld for 20
run CPMSWorld for 20
run World


run addReservation

run addCardToUser

run changeDSO

run changePrice

//checks
check Check_CC_Status



 