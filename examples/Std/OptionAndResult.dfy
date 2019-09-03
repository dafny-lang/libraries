include "../../src/Std.dfy"

module Demo {
  import opened Std

  // ------ Demo for Option ----------------------------
  // We use Option when we don't need to pass around a reason for the failure,
  // ie when just 'None' is sufficient:

  class MyMap<K(==), V> {
    var m: map<K, V>
    constructor () {
      m := map[];
    }
    function method Get(k: K): Option<V>
      reads this
    {
      if k in m then Some(m[k]) else None()
    }
    method Put(k: K, v: V) 
      modifies this
    {
      this.m := this.m[k := v];
    }
  }

  method TestMyMap() {
    var m := new MyMap<string, string>();
    m.Put("message", "Hello");
    var o: Option<string> := m.Get("message");
    if o.Some? {
      print o.get, "\n";
    } else {
      print "oops\n";
    }

    m.Put("name", "Dafny");
    var r: Result<string> := FindName(m);
    if r.Success? {
      print r.value, "\n";
    } else {
      print "Error: ", r.error, "\n";
    }
  }

  // Sometimes we want to go from Option to Result:
  method FindName(m: MyMap<string, string>) returns (res: Result<string>) {
    // Will return a default error message in case of None:
    res := m.Get("name").ToResult();
    // We can also match on the option to write a custom error:
    match m.Get("name")
    case Some(n) => res := Success(n);
    case None => res := Failure("'name' was not found");
  }


  // ------ Demo for Result ----------------------------
  // We use Result when we want to give a reason for the failure:

  class MyFilesystem {
    var files: map<string, string>
    constructor() {
      files := map[];
    }

    // Result<()> is used to return a Result without any data
    method WriteFile(path: string, contents: string) returns (res: Result<()>)
      modifies this
    {
      if path in files {
        files := files[path := contents];
        res := Success(()); // `()` is the only value of type `()`
      } else {
        // The "Result" datatype allows us to give precise error messages
        // instead of just "None"
        res := Failure("File not found, use 'Create' before");
      }
    }

    method CreateFile(path: string) returns (res: Result<()>)
      modifies this
    {
      if path in files {
        res := Failure("File already exists");
      } else {
        files := files[path := ""];
        res := Success(());
      }
    }

    method ReadFile(path: string) returns (res: Result<string>) {
      if path in files {
        res := Success(files[path]);
      } else {
        res := Failure("File not found");
      }
    }
  }

  method TestMyFilesystem() returns (r: Result<()>) {
    var fs := new MyFilesystem();
    var _ :- fs.CreateFile("test.txt");
    var _ :- fs.WriteFile("test.txt", "Test dummy file");
    var contents: string :- fs.ReadFile("test.txt");
    print contents, "\n";
  }

  method Main() {
    TestMyMap();
    var outcome: Result<()> := TestMyFilesystem();
    if outcome.Failure? {
      print outcome.error, "\n";
    }
  }
}
