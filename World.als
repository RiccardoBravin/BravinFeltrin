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
    employees: some CPOEmployee
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



//assertion

assert Correct_numbering{
    #chargingStation = #Coordinate and
    no disj u1, u2:User | u1.email = u2.email
    
}

//run
run {
    all s:String | s in "a"+"b"+"c"+"d"
    //#Reservation > 0
}

check Correct_numbering

check{
    #DSO < 1
    #ChargingColumn >= #ChargingStation 
}
 