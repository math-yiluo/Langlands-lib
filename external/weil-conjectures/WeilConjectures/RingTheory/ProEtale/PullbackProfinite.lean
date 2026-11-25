/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.Topology.DiscreteQuotient
public import Mathlib.Topology.Separation.Regular
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import WeilConjectures.RingTheory.ProEtale.IndZariski
public import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant

/-!
# The prime spectrum of rings of locally constant functions

Let `R` be a ring and `T` a profinite space. In this file we show that the ring
`LocallyConstant T R` of locally constant functions `T → R` satisfies
`Spec (LocallyConstant T R) ≃ₜ T × Spec R` and is ind-Zariski over `R`.

The ring `LocallyConstant T R` is the filtered colimit of the finite products
`LocallyConstant S R ≃ (S → R)` over the discrete quotients `S` of `T`, and the
homeomorphism is the topological incarnation of
`Spec (colim_S (S → R)) = lim_S (S × Spec R) = T × Spec R`; both facts are however
proved directly. This is the input for the construction of Stacks Tag 097D
(`def:modify-pi0-profinite` in the blueprint): modifying the connected components of
`Spec R` along a continuous map `T → π₀(Spec R)`, see
`WContractification.PullbackProfinite` in `Proetale.Algebra.WContractible`.

## Main declarations

* `LocallyConstant.toPrimeSpectrum`: the map `T × Spec R → Spec (LocallyConstant T R)`
  sending `(t, p)` to the prime of functions whose value at `t` lies in `p`.
* `LocallyConstant.homeomorphPrimeSpectrum`: for `T` profinite, `toPrimeSpectrum` is a
  homeomorphism.
* `LocallyConstant.instIndZariski`: `LocallyConstant T R` is ind-Zariski over `R`, being
  the filtered colimit of the finite products `LocallyConstant S R ≃ (S → R)` over the
  discrete quotients `S` of `T`.
-/

@[expose] public section

universe u

open PrimeSpectrum TopologicalSpace

namespace LocallyConstant

variable {T : Type*} [TopologicalSpace T] {R : Type*} [CommRing R]

/-!
### Characteristic functions of clopen subsets
-/

section CharFn

variable {U V : Set T}






end CharFn

/-!
### The prime spectrum of `LocallyConstant T R`
-/

variable (t : T) (p : PrimeSpectrum R)







section Profinite

variable [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T]







end Profinite

/-!
### `LocallyConstant T R` is ind-Zariski over `R`

The ring of locally constant functions is the filtered colimit of the algebras
`LocallyConstant S R ≃ (S → R)` of functions on the (finite) discrete quotients `S`
of `T`. Since finite products of copies of `R` are ind-Zariski over `R`, so is the
colimit.
-/

section IndZariski

open CategoryTheory CategoryTheory.Limits

/-- For a discrete space, locally constant functions are just functions. -/
@[simps]
def algEquivPi (R : Type*) [CommRing R] (S : Type*) [TopologicalSpace S]
    [DiscreteTopology S] :
    LocallyConstant S R ≃ₐ[R] (S → R) where
  toFun f := ⇑f
  invFun g := ⟨g, IsLocallyConstant.of_discrete g⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

variable (R : Type u) [CommRing R] (T : Type u) [TopologicalSpace T] [CompactSpace T]

/-- The filtered diagram of the algebras of functions on the (finite) discrete
quotients of `T`. -/
@[simps]
noncomputable def discreteQuotientDiag : (DiscreteQuotient T)ᵒᵖ ⥤ CommAlgCat R where
  obj S := .of R (LocallyConstant S.unop R)
  map {S S'} h := CommAlgCat.ofHom <| comapₐ R
    ⟨DiscreteQuotient.ofLE h.unop.le, DiscreteQuotient.ofLE_continuous h.unop.le⟩
  map_id S := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro f
    ext x
    exact congrArg f (DiscreteQuotient.ofLE_refl_apply x)
  map_comp {S S' S''} h h' := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro f
    ext x
    exact congrArg f (DiscreteQuotient.ofLE_ofLE h'.unop.le h.unop.le x).symm

/-- The cocone over `discreteQuotientDiag` with apex `LocallyConstant T R`, given by
pulling back functions along the quotient projections. -/
@[simps]
noncomputable def discreteQuotientCocone : Cocone (discreteQuotientDiag R T) where
  pt := .of R (LocallyConstant T R)
  ι :=
    { app S := CommAlgCat.ofHom <| comapₐ R ⟨S.unop.proj, S.unop.proj_continuous⟩
      naturality {S S'} h := by
        dsimp only [discreteQuotientDiag]
        apply CommAlgCat.hom_ext
        apply AlgHom.ext
        intro f
        apply LocallyConstant.ext
        intro t
        exact congrArg (fun x ↦ f x) (DiscreteQuotient.ofLE_proj h.unop.le t) }

/-- The cocone `discreteQuotientCocone` is colimiting: every locally constant function
factors through a discrete quotient, and two functions on quotients agreeing on `T`
agree on a common refinement. -/
noncomputable def isColimitDiscreteQuotientCocone :
    IsColimit (discreteQuotientCocone R T) := by
  haveI : ReflectsColimitsOfShape (DiscreteQuotient T)ᵒᵖ (forget (CommAlgCat R)) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  apply isColimitOfReflects (forget (CommAlgCat R))
  refine Types.FilteredColimit.isColimitOf' _ _ ?_ ?_
  · intro f
    refine ⟨Opposite.op f.discreteQuotient, f.lift, ?_⟩
    change f = comapₐ R ⟨f.discreteQuotient.proj, f.discreteQuotient.proj_continuous⟩ f.lift
    apply LocallyConstant.ext
    intro t
    exact (congrFun f.lift_comp_proj t).symm
  · intro S g₁ g₂ h
    refine ⟨S, 𝟙 S, ?_⟩
    suffices hg : g₁ = g₂ by rw [hg]
    refine comap_injective ⟨S.unop.proj, S.unop.proj_continuous⟩ S.unop.proj_surjective ?_
    exact h

/-- `LocallyConstant T R` as the filtered colimit of the algebras of functions on the
discrete quotients of `T`. -/
noncomputable def discreteQuotientColimitPresentation :
    ColimitPresentation (DiscreteQuotient T)ᵒᵖ (CommAlgCat.of R (LocallyConstant T R)) where
  diag := discreteQuotientDiag R T
  ι := (discreteQuotientCocone R T).ι
  isColimit := isColimitDiscreteQuotientCocone R T

instance (S : DiscreteQuotient T) : Algebra.IndZariski R (LocallyConstant S R) :=
  Algebra.IndZariski.of_equiv (R := R) (S := (S → R)) (T := LocallyConstant S R)
    (algEquivPi R S).symm

/-- The ring of locally constant functions on a compact space is ind-Zariski. This is
the algebra `A^S` of Stacks 097D (for `S = T` profinite), obtained as the filtered
colimit of the finite products `S → R` over the discrete quotients `S` of `T`. -/
instance instIndZariski : Algebra.IndZariski R (LocallyConstant T R) :=
  Algebra.IndZariski.of_colimitPresentation (R := R) (S := LocallyConstant T R)
    (discreteQuotientColimitPresentation R T) fun S ↦
    inferInstanceAs (Algebra.IndZariski R (LocallyConstant S.unop R))

end IndZariski

end LocallyConstant
