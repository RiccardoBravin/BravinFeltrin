//Signatures of all main objects

abstract sig Bool{}
one sig True extends Bool{}
one sig False extends Bool{}

abstract sig ChargeRate{}
one sig Slow extends ChargeRate{}
one sig Fast extends ChargeRate{}
one sig Rapid extends ChargeRate{}

abstract sig EnergyType{}
one sig Green extends EnergyType{}
one sig Carbon extends EnergyType{}
one sig Nuclear extends EnergyType{}

//simplified date signature
sig Date{
    val : one Int
}



sig Email{

}

sig Card{  

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

    name: one String,
    chargingColumns: some ChargingColumn,
    supplier: one DSO
}

sig DSO{  
}

sig ChargingColumn{
    type: one ChargeRate
}

sig CPO{
    employees: some CPOEmployee,
    chargingStations: some ChargingStation
}

sig CPOEmployee{
    workPlace: one ChargingStation
}



//Constraints to be satisfied by the model




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
    all d:Date | d in Reservation.time
}


//each chargingColumn is always in one and only one chargingStation
fact{
    all c:ChargingColumn | no disj c1,c2:ChargingStation | c in c1.chargingColumns and c in c2.chargingColumns
    all c:ChargingColumn | c in ChargingStation.chargingColumns
}



//each employee must work for one and only one CPO
fact{
    all e:CPOEmployee | no disj c1,c2:CPO | e in c1.employees and e in c2.employees
    all e:CPOEmployee | e in CPO.employees
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




//Worlds


pred World{
    #Reservation = 1
    #User = 1
    #Card = 1
    #Email = 1
    #ChargingStation = 1
    #ChargingColumn = 1
    #DSO = 1
}

//run

run {
    
    //#Reservation = 1 
}


run World




 