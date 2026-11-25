/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.FieldTheory.SeparableClosure
public import WeilConjectures.SixFunctors.ProEtale.GenericPoint

/-!
# The pro-étale cover of a scheme over a field by its base change to a separable closure

Let `X` be a scheme over a field `k` and `kˢᵉᵖ` a separable closure of `k`. The base change
`X ×_k Spec kˢᵉᵖ ⟶ X` is surjective, quasi-compact and weakly étale, `kˢᵉᵖ` being an ind-étale
`k`-algebra; hence it is a pro-étale cover of `X`
(`AlgebraicGeometry.Scheme.sepClosureCover`). Over it, every ingredient defined from roots of
unity, such as the Tate twists, can be trivialized.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {k : Type u} [Field k]

/-- The morphism `Spec kˢᵉᵖ ⟶ Spec k`. -/
noncomputable abbrev specSepClosureHom (k : Type u) [Field k] :
    Spec (.of (SeparableClosure k)) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (SeparableClosure k)))

instance (k : Type u) [Field k] : WeaklyEtale (specSepClosureHom k) := by
  have := Algebra.IndEtale.of_isSeparable k (SeparableClosure k)
  infer_instance

instance (k : Type u) [Field k] : Surjective (specSepClosureHom k) :=
  ⟨fun _ ↦ ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩

instance (k : Type u) [Field k] : QuasiCompact (specSepClosureHom k) :=
  inferInstance

/-- The **pro-étale cover of `X` by `X ×_k Spec kˢᵉᵖ`**, for a scheme `X` over a field `k`. -/
noncomputable def sepClosureCover (f : X ⟶ Spec (.of k)) :
    Scheme.Cover.{u} Scheme.proetalePrecoverage X :=
  Precoverage.ZeroHypercover.singleton (pullback.fst f (specSepClosureHom k))
    (Scheme.Hom.singleton_mem_propQCPrecoverage (P := @WeaklyEtale) inferInstance)

end AlgebraicGeometry.Scheme
