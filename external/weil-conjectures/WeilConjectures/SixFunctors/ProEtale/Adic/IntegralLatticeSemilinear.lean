/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.IntegralLatticeIntegrality
public import WeilConjectures.SixFunctors.ProEtale.Adic.IntegralLatticeKernel
public import WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarConstantFinitenessStratum

/-!
# Semilinearity of integral identifications from the integrality of the lattices

Let `g : T ⟶ Y` be quasi-compact and quasi-separated. The semilinearity of the integral
identifications (`AlgebraicGeometry.ProEtale.IntegralLatticeSemilinear`), for `ℤ_ℓ → 𝒪_E`
surjective (`E = ℚ_ℓ`), reduces to the **integrality** of the lattices
(`AlgebraicGeometry.ProEtale.IntegralLatticeIntegral`): for every weakly étale `p : S ⟶ S₀` and
`j : S₀ ⟶ Y`, the multiplication by `f ∈ C(U, 𝒪_E)` on the sections over `U` of
`p^* j^* Rⁱg_* ℚ̄_ℓ,T` preserves the image of the sections of `(p ≫ j)^* Rⁱg_* 𝒪_{E,T}` under
`κ : (p ≫ j)^* Rⁱg_* 𝒪_{E,T} ⟶ (p ≫ j)^* Rⁱg_* ℚ̄_ℓ,T ≅ p^* j^* Rⁱg_* ℚ̄_ℓ,T`
(`AlgebraicGeometry.ProEtale.integralLatticeToAdicHom`). This is
`AlgebraicGeometry.ProEtale.integralLatticeSemilinear_of_integralLatticeIntegral`, combining
`AlgebraicGeometry.ProEtale.AdicSheaf.map_smul_of_integral` with the torsion of the kernels
(`AlgebraicGeometry.ProEtale.exists_pow_smul_eq_zero_of_integralLatticeSections_eq_zero`).
Consequently `Rg_* ℚ̄_ℓ,T` is bounded with constructible cohomology sheaves as soon as the
lattices are integral
(`AlgebraicGeometry.ProEtale.finiteLowerStar_singleFunctor_unit_of_integralLatticeIntegral`).
-/

@[expose] public section
universe u

open CategoryTheory Limits Opposite PadicAlgCl

namespace AlgebraicGeometry.ProEtale

open Scheme

section Hom

variable {l : ℕ} [Fact l.Prime] {T Y S : Scheme.{u}} {g : T ⟶ Y} {i : ℕ} {q : S ⟶ Y}
  {F : AdicSheaf l S} (e : AdicAbIdentification g i F q) (E : FiniteIntermediateField l)

/-- The morphism `q^* Rⁱg_* 𝒪_{E,T} ⟶ q^* Rⁱg_* ℚ̄_ℓ,T ≅ F` of abelian sheaves attached to an
identification `e`. -/
noncomputable def integralLatticeToAdicHom :
    (q)^*[Ab.{u + 1}].obj (((g)_*[Ab.{u + 1}].rightDerived i).obj
      ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (padicIntegersSheaf T l E.1))) ⟶
    (sheafCompose (Scheme.ProEt.topology S) (forget₂ (WeilCoefficients.{u} l) Ab.{u + 1})).obj
      F.X :=
  (q)^*[Ab.{u + 1}].map (((g)_*[Ab.{u + 1}].rightDerived i).map
    (adicConstantSheafLeg T l E 0)) ≫ e.iso.inv

lemma integralLatticeSectionsOfIdentification_eq {M : Type} [TopologicalSpace M] [AddCommGroup M]
    [IsTopologicalAddGroup M]
    (θ : continuousMapAddSheaf S M ⟶ (q)^*[Ab.{u + 1}].obj (((g)_*[Ab.{u + 1}].rightDerived i).obj
      ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (padicIntegersSheaf T l E.1))))
    (U : S.ProEt) (m : C(U.left, M)) :
    integralLatticeSectionsOfIdentification e E θ U m =
      (integralLatticeToAdicHom e E).hom.app (op U) (θ.hom.app (op U) (ULift.up m)) :=
  rfl

end Hom

variable (l : ℕ) [Fact l.Prime]

/-- **Integrality of the lattices `Rⁱg_* 𝒪_{E,T}`**: for every weakly étale `p : S ⟶ S₀` and every
`j : S₀ ⟶ Y`, the multiplication by a function `f ∈ C(U, 𝒪_E)` on the sections over `U` of
`p^* j^* Rⁱg_* ℚ̄_ℓ,T` preserves the image of the sections of `(p ≫ j)^* Rⁱg_* 𝒪_{E,T}`. -/
def IntegralLatticeIntegral {T Y : Scheme.{u}} (g : T ⟶ Y) (i : ℕ)
    (E : FiniteIntermediateField l) : Prop :=
  letI := integersTopology l E
  ∀ ⦃S S₀ : Scheme.{u}⦄ (p : S ⟶ S₀) [WeaklyEtale p] (j : S₀ ⟶ Y) (U : S.ProEt)
    (f : C(U.left, integers l E.1))
    (a : ((p ≫ j)^*[Ab.{u + 1}].obj (((g)_*[Ab.{u + 1}].rightDerived i).obj
      ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        (padicIntegersSheaf T l E.1)))).obj.obj (op U)),
    ∃ b, (integralLatticeToAdicHom ((AdicAbIdentification.ofUpperStar g i j).upperStar p)
        E).hom.app (op U) b =
      AdicSheaf.sectionAct _ (ULift.up (AdicSheaf.ringValuedFunction _
        (continuous_algebraMap_integers l E.1) (algebraMap_integers_mem l E.1) f))
        ((integralLatticeToAdicHom ((AdicAbIdentification.ofUpperStar g i j).upperStar p)
          E).hom.app (op U) a)


/-- **Integrality implies semilinearity**: if `ℤ_ℓ → 𝒪_E` is surjective (e.g. `E = ℚ_ℓ`) and the
lattices `Rⁱg_* 𝒪_{E,T}` are integral for the action of the `𝒪_E`-valued functions, then the
integral identifications are semilinear. -/
theorem integralLatticeSemilinear_of_integralLatticeIntegral {T Y : Scheme.{u}} (g : T ⟶ Y)
    [QuasiCompact g] [QuasiSeparated g] (i : ℕ) (E : FiniteIntermediateField l)
    (hsurj : Function.Surjective (integersPadicIntHom l E.1))
    (h : IntegralLatticeIntegral l g i E) : IntegralLatticeSemilinear l g i E := by
  intro S S₀ p _ j M _ _ _ τ _ _ _ _ hι hτ θ _ U f m
  subst hτ
  let e := (AdicAbIdentification.ofUpperStar (l := l) g i j).upperStar p
  have hθ (V : S.ProEt) : Function.Bijective (θ.hom.app (op V)) :=
    (ConcreteCategory.isIso_iff_bijective _).1 (inferInstanceAs (IsIso
      ((((sheafToPresheaf _ _).mapIso (asIso θ)).app (op V)).hom)))
  refine AdicSheaf.map_smul_of_integral E hι _ rfl hsurj
    (integralLatticeSectionsOfIdentification e E θ)
    (fun _ _ f m ↦ AdicSheaf.sectionsOfHom_comp _ _ f m)
    (exists_pow_smul_eq_zero_of_integralLatticeSections_eq_zero e E θ hsurj)
    (fun V f m ↦ ?_) U f m
  obtain ⟨b, hb⟩ := h p j V f (θ.hom.app (op V) (ULift.up m))
  obtain ⟨⟨e'⟩, he'⟩ := (hθ V).2 b
  refine ⟨e', ?_⟩
  rw [integralLatticeSectionsOfIdentification_eq e E θ V e', he', hb]
  rfl

section Finiteness

variable {l} {k : Type u} [Field k] {T Y : Scheme.{u}} (g : T ⟶ Y) [QuasiCompact g]
  [QuasiSeparated g] (aT : T ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aT]
  [QuasiCompact aT] [LocallyOfFiniteType aY] [QuasiCompact aY] (hg : g ≫ aY = aT) (d : ℕ)
  (hd : topologicalKrullDim T ≤ (d : WithBot ℕ∞))

variable (l) in
include hg hd in
/-- **Finiteness for the constant `ℓ`-adic sheaf, up to integrality.** Let `g : T ⟶ Y` be
quasi-compact and quasi-separated between schemes of finite type over a field, with `dim T ≤ d`,
and `ℓ` invertible on `T`. If the lattices `Rⁱg_* ℤ_ℓ,T` are integral, then `Rg_* ℚ̄_ℓ,T` is
bounded with constructible cohomology sheaves. -/
theorem finiteLowerStar_singleFunctor_unit_of_integralLatticeIntegral
    [HasInvertibleExponent (integersShrink.{u} l (finiteIntermediateFieldBot l).1 ⧸
      integersShrinkIdeal.{u} l (finiteIntermediateFieldBot l).1) T]
    (hint : ∀ i, IntegralLatticeIntegral l g i (finiteIntermediateFieldBot l)) :
    finiteLowerStar l g ((DerivedCategory.singleFunctor _ 0).obj (AdicSheaf.unit l T)) :=
  finiteLowerStar_singleFunctor_unit_of_integralLatticeSemilinear l g aT aY hg d hd
    fun i ↦ integralLatticeSemilinear_of_integralLatticeIntegral l g i _
      (surjective_integersPadicIntHom_bot l) (hint i)

end Finiteness

end AlgebraicGeometry.ProEtale
