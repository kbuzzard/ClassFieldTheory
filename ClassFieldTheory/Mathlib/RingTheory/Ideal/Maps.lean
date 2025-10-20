import Mathlib.RingTheory.Ideal.Maps

lemma Ideal.map_injective {R S : Type*} [CommSemiring R] [CommSemiring S]
    {E : Type*} [EquivLike E R S] [RingEquivClass E R S] (e : E) :
    Function.Injective (Ideal.map e) := fun x y h ↦ by
  rw [← Ideal.comap_map_of_bijective e (EquivLike.bijective e) (I := x), h,
    Ideal.comap_map_of_bijective e (EquivLike.bijective e)]
