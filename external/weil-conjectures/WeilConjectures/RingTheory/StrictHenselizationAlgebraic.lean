/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.IsStrictHenselization
public import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Elements of a strict henselization are algebraic

Let `A` be a local domain and `C` a domain which is a strict henselization of `A`. Then every
element of `C` is algebraic over `A`.

An étale `A`-algebra `S` becomes finite over the fraction field `Frac A` after base change, so
the image of `S` in any domain `C` receiving an injective map from `A` consists of algebraic
elements. The elements of `C` algebraic over `A` form a subalgebra; the legs of the colimit
cocone land in it, so the universal property gives a retraction of its inclusion.

## Main results

- `isAlgebraic_algHom_of_etale`: the image of an étale algebra in a domain is algebraic.
- `Algebra.IsStrictHenselization.isAlgebraic`: a strict henselization which is a domain is
  algebraic over the base.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TensorProduct

/-- If `S` is an étale `A`-algebra over a domain `A` and `φ : S →ₐ[A] C` is a map to a domain `C`
with `A → C` injective, then every element in the image of `φ` is algebraic over `A`: the base
change of `S` to `Frac A` is étale, hence finite, over the field `Frac A`, and `φ` extends to it
with values in `Frac C`. -/
theorem isAlgebraic_algHom_of_etale {A S C : Type*} [CommRing A] [IsDomain A] [CommRing S]
    [Algebra A S] [Algebra.Etale A S] [CommRing C] [IsDomain C] [Algebra A C]
    (hinj : Function.Injective (algebraMap A C)) (φ : S →ₐ[A] C) (s : S) :
    IsAlgebraic A (φ s) := by
  let L := FractionRing C
  let K := FractionRing A
  let ι : C →ₐ[A] L := IsScalarTower.toAlgHom A C L
  have hι : Function.Injective ι := IsFractionRing.injective C L
  have : FaithfulSMul A L := by
    rw [faithfulSMul_iff_algebraMap_injective, IsScalarTower.algebraMap_eq A C L]
    exact hι.comp hinj
  let : Algebra K L := FractionRing.liftAlgebra A L
  let ψ : K ⊗[A] S →ₐ[K] L :=
    Algebra.TensorProduct.lift (Algebra.ofId K L) (ι.comp φ) fun _ _ ↦ mul_comm _ _
  have : Module.Finite K (K ⊗[A] S) := Module.Finite.of_quasiFinite
  have hs : IsAlgebraic K (ψ (1 ⊗ₜ s)) :=
    (Algebra.IsIntegral.isAlgebraic.isAlgebraic (1 ⊗ₜ[A] s : K ⊗[A] S)).algHom ψ
  have hψ : ψ (1 ⊗ₜ s) = ι (φ s) :=
    (Algebra.TensorProduct.lift_tmul (Algebra.ofId K L) (ι.comp φ) _ 1 s).trans (by simp)
  rw [← IsFractionRing.isAlgebraic_iff A K L, hψ] at hs
  rwa [← isAlgebraic_algHom_iff ι hι]

namespace Algebra

/-- **Elements of a strict henselization are algebraic.** If the strict henselization `C` of a
local domain `A` is a domain, then `C` is algebraic over `A`. The legs of the colimit cocone take
values in the subalgebra of elements algebraic over `A` (`isAlgebraic_algHom_of_etale`), so the
universal property of the colimit gives a retraction of the inclusion of this subalgebra. If
`A → C` is not injective, a nonzero element of its kernel is a nonzero constant polynomial
annihilating every element. -/
theorem IsStrictHenselization.isAlgebraic {A K C : Type u} [CommRing A] [IsDomain A]
    [IsLocalRing A] [Field K] [Algebra (IsLocalRing.ResidueField A) K]
    [IsSepClosure (IsLocalRing.ResidueField A) K] [Algebra A K]
    [IsScalarTower A (IsLocalRing.ResidueField A) K] [CommRing C] [IsDomain C] [Algebra A C]
    (hC : IsStrictHenselization A K C) : Algebra.IsAlgebraic A C := by
  by_cases hinj : Function.Injective (algebraMap A C)
  swap
  · rw [injective_iff_map_eq_zero] at hinj
    push Not at hinj
    obtain ⟨a, ha, ha0⟩ := hinj
    refine ⟨fun x ↦ ⟨Polynomial.C a, Polynomial.C_ne_zero.2 ha0, ?_⟩⟩
    simp [ha]
  let P : ObjectProperty (Over (CommAlgCat.of A K)) := fun X ↦ Etale A X.left
  let D := P.ι ⋙ Over.forget (CommAlgCat.of A K)
  obtain ⟨c, ⟨hc⟩, ⟨e⟩⟩ := hC
  let cC : Cocone D := c.extend e.hom
  have hcC : IsColimit cC := hc.extendIso e.hom
  let T := Subalgebra.algebraicClosure A C
  have hT (i : P.FullSubcategory) (x : D.obj i) : (cC.ι.app i).hom x ∈ T := by
    have : Etale A (D.obj i) := i.property
    exact (Subalgebra.mem_algebraicClosure A C).2
      (isAlgebraic_algHom_of_etale hinj (cC.ι.app i).hom x)
  let d : Cocone D :=
    { pt := CommAlgCat.of A T
      ι :=
        { app i := CommAlgCat.ofHom ((cC.ι.app i).hom.codRestrict T (hT i))
          naturality {i j} f := by
            ext x
            exact Subtype.ext (DFunLike.congr_fun (congrArg CommAlgCat.Hom.hom (cC.w f)) x) } }
  have he : hcC.desc d ≫ CommAlgCat.ofHom T.val = 𝟙 _ := by
    refine hcC.hom_ext fun i ↦ ?_
    rw [← Category.assoc, hcC.fac]
    rfl
  refine ⟨fun x ↦ ?_⟩
  have hx : ((hcC.desc d).hom x : C) = x :=
    DFunLike.congr_fun (congrArg CommAlgCat.Hom.hom he) x
  exact (Subalgebra.mem_algebraicClosure A C).1 (hx ▸ ((hcC.desc d).hom x).property)

end Algebra
