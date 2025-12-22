// This module is responsible for desugaring datatypes into B3 constructs:
//   * type declarations for the datatype
//   * tagger declarations for the datatype
//   * constructor functions (tagged)

module DatatypeDesugaring {
  import opened Ast
  import opened Std.Wrappers
  import opened Basics
  import Types
  import Raw = RawAst
  import TypeResolver

  export
    provides DesugarDatatype
    provides CreateTagger, CreateConstructors
    provides Ast, Wrappers

  // Main entry point for desugaring a single datatype (basic version for task 1)
  // Now creates TypeDecl, Tagger, and Constructor functions
  method DesugarDatatype(b3: Raw.Program, dt: Raw.DatatypeDecl, typeMap: map<string, TypeDecl>) 
    returns (r: Result<(TypeDecl, Function, seq<Function>), string>)
    requires dt.WellFormed(b3)
    ensures r.Success? ==> 
      var (typ, tagger, constructors) := r.value;
      && fresh(typ) && fresh(tagger) && fresh(constructors)
      && typ.Name == dt.name
      && tagger.Name == dt.name + "Tag"
      && tagger.WellFormedAsTagger()
      && tagger.FromDatatype == Some(dt.name)
      && (forall func: Function <- constructors :: func.WellFormed())
      && (forall func: Function <- constructors :: func.FromDatatype == Some(dt.name))
      && |constructors| == |dt.constructors|
  {
    // Step 1: Create the type declaration
    var typ := new TypeDecl(dt.name);
    
    // Step 2: Create the tagger
    var tagger :- CreateTagger(dt, typ);
    
    // Step 3: Create constructor functions
    var constructors :- CreateConstructors(b3, dt, typ, tagger, typeMap);
    
    return Success((typ, tagger, constructors));
  }

  // Create tagger for the datatype
  method CreateTagger(dt: Raw.DatatypeDecl, typ: TypeDecl) returns (r: Result<Function, string>)
    ensures r.Success? ==> var tag := r.value;
        && fresh(tag) 
        && tag.WellFormedAsTagger()
        && tag.Name == dt.name + "Tag"
        && tag.Parameters[0].typ == UserType(typ)
        && tag.FromDatatype == Some(dt.name)
  {
    var taggerName := dt.name + "Tag";
    
    Raw.SurelyLegalVariableName("subject");
    var parameter := new FParameter("subject", false, UserType(typ));
    var tagger := new Function(taggerName, [parameter], TagType, None, Some(dt.name));
    
    return Success(tagger);
  }

  // Create constructor functions
  method CreateConstructors(b3: Raw.Program, dt: Raw.DatatypeDecl, typ: TypeDecl, tagger: Function, typeMap: map<string, TypeDecl>) 
    returns (r: Result<seq<Function>, string>)
    requires dt.WellFormed(b3)
    requires tagger.WellFormedAsTagger()
    requires tagger.Parameters[0].typ == UserType(typ)
    ensures r.Success? ==> fresh(r.value)
    ensures r.Success? ==> forall func: Function <- r.value :: func.WellFormed()
    ensures r.Success? ==> forall func: Function <- r.value :: func.FromDatatype == Some(dt.name)
    ensures r.Success? ==> |r.value| == |dt.constructors|
  {
    var constructors: seq<Function> := [];
    
    for i := 0 to |dt.constructors|
      invariant fresh(constructors)
      invariant forall func: Function <- constructors :: func.WellFormed()
      invariant forall func: Function <- constructors :: func.FromDatatype == Some(dt.name)
      invariant |constructors| == i
    {
      var ctor := dt.constructors[i];
      var ctorFunc :- CreateConstructorFunction(b3, ctor, dt.name, typ, tagger, typeMap);
      constructors := constructors + [ctorFunc];
    }
    
    return Success(constructors);
  }

  method CreateConstructorFunction(b3: Raw.Program, ctor: Raw.Constructor, datatypeName: string, typ: TypeDecl, tagger: Function, typeMap: map<string, TypeDecl>) 
    returns (r: Result<Function, string>)
    requires ctor.WellFormed(b3)
    requires tagger.WellFormedAsTagger()
    requires tagger.Parameters[0].typ == UserType(typ)
    ensures r.Success? ==> fresh(r.value) && r.value.WellFormed()
    ensures r.Success? ==> r.value.FromDatatype == Some(datatypeName)
  {
    // Create parameters (all injective for constructors)
    var parameters: seq<FParameter> := [];
    for i := 0 to |ctor.fields|
      invariant fresh(parameters)
      invariant forall p : FParameter <- parameters :: p.WellFormed()
      invariant forall j, k :: 0 <= j < k < |parameters| ==> parameters[j].name != parameters[k].name
      invariant forall j, p <- parameters :: i <= j < |ctor.fields| ==> p.name != ctor.fields[j].name
    {
      var field := ctor.fields[i];
      //TODO: will we need precondition that all ADTs here? or restrictions for inhabited?
      var fieldType :- TypeResolver.ResolveType(field.typ, typeMap);
      var param := new FParameter(field.name, true, fieldType);
      
      parameters := parameters + [param];
    }
    
    var ctorFunc := new Function(ctor.name, parameters, UserType(typ), Some(tagger), Some(datatypeName));
    
    return Success(ctorFunc);
  }
}
