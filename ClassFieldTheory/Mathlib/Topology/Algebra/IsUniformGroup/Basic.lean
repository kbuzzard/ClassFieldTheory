module

public import Mathlib.Topology.Algebra.IsUniformGroup.Basic

public section

instance IsUniformAddGroup.addSubgroupClass {α S : Type*} [UniformSpace α] [AddGroup α]
    [SetLike S α] [AddSubgroupClass S α] [IsUniformAddGroup α] (s : S) :
    IsUniformAddGroup s :=
  AddSubgroup.isUniformAddGroup <| .ofClass s
