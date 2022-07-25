// RUN: %dafny /compile:3 "%s"

include "../src/NonVariantWrappers.dfy"

module Demo {
  import opened Wrappers

  // Illustrating what the non-variant versions of Wrappers datatypes
  // don't support, but also how to work around it.

  trait Vehicle {
  }
  class Car extends Vehicle {
    constructor() {}
  }

  trait Error {
  }
  class FlatTireError extends Error {
    constructor() {}
  }

  method Main() {
    var myCar: Car := new Car();
    var myFlatTire: FlatTireError := new FlatTireError();

    // This is just fine
    var generalSuccess: Result<Vehicle, Error> := Success(myCar);
    var generalFailure: Result<Vehicle, Error> := Failure(myFlatTire);

    // These are the only patterns that don't work without variance.
    // But most of the time you only need to pass around the more general Result type,
    // so the workaround is just to never create values of more specific types such as Result<Car, Error>
    var carSuccess: Result<Car, Error> := Success(myCar);
    var flatTireFailure: Result<Vehicle, FlatTireError> := Failure(myFlatTire);
    // RHS (of type Result<Car, Error>) not assignable to LHS (of type Result<Vehicle, Error>) (non-variant type parameter 0 would require Vehicle = Car)
    // generalSuccess := carSuccess;
    // RHS (of type Result<Vehicle, FlatTireError>) not assignable to LHS (of type Result<Vehicle, Error>) (non-variant type parameter 1 would require Error = FlatTireError)
    // generalFailure := flatTireFailure;

    // You can also always "upcast" by creating new values
    generalSuccess := Success(carSuccess.value);
    generalFailure := Failure(flatTireFailure.error);
  }
}
