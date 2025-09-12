module Types {
  // Types

  type TypeName = string

  const BoolTypeName := "bool"
  const IntTypeName := "int"
  const TagTypeName := "tag"
  const BuiltInTypes: set<TypeName> := {BoolTypeName, IntTypeName, TagTypeName}
}