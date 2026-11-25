/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.TraceClass

/-!

# Specialization of trace classes

Let `c = (c₁, c₂) : C ⟶ X × X` be an endocorrespondence of `(X, K)` over `k` with fixed locus
`ι : Fix(c) ⟶ C`, `d = ι ≫ c₁`, and let `c' : C' ⟶ X' × X'` be an endocorrespondence of
`(X', K')` over a second field `k'`, with fixed locus `ι' : Fix(c') ⟶ C'`. In Varshavsky's proof
of the contracting theorem (*Lefschetz–Verdier trace formula and a generalization of a theorem of
Fujiwara*, §1.4–§2; blueprint `proposition-specialization-trace-class`), `c` is the generic fibre
and `c'` the special fibre of a correspondence over a strictly henselian trait, and nearby cycles
`Ψ` relate the six functors on the two fibres through the exchange maps (blueprint
`prose-E-15`)
```
χ_ι : Ψ_C Rι_* ⟶ Rι'_* Ψ_F,     χ_Δ : Ψ_{X×X} RΔ_* ⟶ RΔ'_* Ψ_X,
β_c : Ψ_C Rc^! ⟶ Rc'^! Ψ_{X×X},  β_d : Ψ_F Rd^! ⟶ Rd'^! Ψ_X,
σ : ℚ̄_ℓ ⟶ Ψ ℚ̄_ℓ,               θ : Ψ ω ⟶ ω'.
```
This file packages these exchange maps and the coherences between them that the trace class
uses (`ProEtale.CondensedRing.Correspondence.TraceSpecialization`), defines the
*specialization* `sp_F(z) = θ_F Ψ_F(z) σ_F` of Borel–Moore sections
(`ProEtale.CondensedRing.Correspondence.TraceSpecialization.sp`), and proves that the
specialization of the trace class factors through the exceptional exchange `β_c` at the kernel
`K ⊠ D_X K` (`ProEtale.CondensedRing.Correspondence.TraceSpecialization.traceMap_specialization`,
the first identity of blueprint `proposition-specialization-trace-class` with the nearby cycles of
the universal kernel left unidentified). In particular the specialization of the trace class
vanishes as soon as `Rc'^! Ψ_{X×X}(K ⊠ D_X K)` does
(`ProEtale.CondensedRing.Correspondence.TraceSpecialization.sp_traceClass_eq_zero`), which is the
mechanism of Varshavsky's vanishing argument (blueprint
`theorem-contracting-correspondences-local-terms`): for the deformation to the normal cone,
`Ψ_{X×X}(K ⊠ D_X K) ≅ Ψ_X K ⊠ D_{X'} Ψ_X K` by Gabber's theorems, so
`Rc'^! Ψ_{X×X}(K ⊠ D_X K) ≅ RHom(Lc₂'^* Ψ_X K, Rc₁'^! Ψ_X K)`, and `Lc₂'^* Ψ_X K = 0`.

## Main definitions

- `ProEtale.CondensedRing.Correspondence.TraceSpecialization`: the exchange maps between a
  generic and a special correspondence used by the trace class, with their coherences.
- `ProEtale.CondensedRing.Correspondence.TraceSpecialization.sp`: the specialization of
  Borel–Moore sections of the fixed loci.

## Main statements

- `ProEtale.CondensedRing.Correspondence.TraceSpecialization.sp_traceClass`: the specialization
  of the trace class is the adjoint of `σ_C`, the mate of `u`, and the specialized trace map.
- `ProEtale.CondensedRing.Correspondence.TraceSpecialization.traceMap_specialization`: the
  specialized trace map factors through `β_c(K ⊠ D_X K)`.
- `ProEtale.CondensedRing.Correspondence.TraceSpecialization.sp_traceClass_eq_zero`: if
  `Rc'^! Ψ_{X×X}(K ⊠ D_X K) = 0`, the specialization of the trace class vanishes.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

namespace Correspondence

variable {ℓ : ℕ} [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {k' : Type u} [Field k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  {K' : Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ℓ⟧}

variable (c : Correspondence ℓ K) (F : c.FixedLocus) (c' : Correspondence ℓ K')
  (F' : c'.FixedLocus)

/-- The *specialization data* of a correspondence `c` over `k` (the generic fibre) to a
correspondence `c'` over `k'` (the special fibre), with fixed loci `F` and `F'` (blueprint
`proposition-specialization-trace-class`, `prose-E-15`): specialization functors
`Ψ_C`, `Ψ_F`, `Ψ_X`, `Ψ_{X×X}` on the bounded constructible derived categories, the
specialization units `σ`, the dualizing maps `θ`, the proper exchanges `χ` for the closed
immersions `ι` and `Δ`, and the exceptional exchanges `β` for the support map `c` and for
`d = ι ≫ c₁`, subject to the three coherences used by the trace class:

* `σ` commutes with the adjunction `Lι^* ⊣ Rι_*` (blueprint
`proposition-specialization-trace-class`, the unit
  identity `χ_ι Ψ_C(η_ι) σ_C = Rι'_*(σ_F) η_ι'`, combined with naturality);
* the composition law `θ_F = d'^! θ_X ∘ β_d(ω_X)` (blueprint
`lemma-compatibilities-base-change-maps` (3),
  read through the composition isomorphisms `Rd^! ω_X ≅ ω_F` of the dualizing complexes);
* the fixed-square identity `Rι'_* β_d ∘ χ_ι ∘ Ψ_C(B) = B' ∘ Rc'^!(χ_Δ) ∘ β_c(RΔ_*)` for the
  base change isomorphisms `B : Rc^! RΔ_* ≅ Rι_* Rd^!` of the fixed squares (blueprint
  `sec-Base-change-for-nearby-cycles` (6)).

For nearby cycles over a strictly henselian trait these are theorems of the nearby-cycles
formalism; here they are the fields of the structure. -/
structure TraceSpecialization where
  /-- the specialization functor `Ψ_C` of the support. -/
  ΨC : Dᵇc(c.C.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ Dᵇc(c'.C.left)⟦Profinite.padicAlgClRingObj ℓ⟧
  /-- the specialization functor `Ψ_F` of the fixed locus. -/
  ΨF : Dᵇc(F.F.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ Dᵇc(F'.F.left)⟦Profinite.padicAlgClRingObj ℓ⟧
  /-- the specialization functor `Ψ_X`. -/
  ΨX : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ℓ⟧
  /-- the specialization functor `Ψ_{X×X}`. -/
  ΨXX : Dᵇc((X ⨯ X).left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
    Dᵇc((X' ⨯ X').left)⟦Profinite.padicAlgClRingObj ℓ⟧
  /-- the specialization unit `σ_C : ℚ̄_ℓ ⟶ Ψ_C ℚ̄_ℓ`. -/
  σC : 𝟙_ _ ⟶ ΨC.obj (𝟙_ _)
  /-- the specialization unit `σ_F : ℚ̄_ℓ ⟶ Ψ_F ℚ̄_ℓ`. -/
  σF : 𝟙_ _ ⟶ ΨF.obj (𝟙_ _)
  /-- the dualizing map `θ_X : Ψ_X ω_X ⟶ ω_X'`. -/
  θX : ΨX.obj (dualizingComplex' ℓ X) ⟶ dualizingComplex' ℓ X'
  /-- the dualizing map `θ_F : Ψ_F ω_F ⟶ ω_F'`. -/
  θF : ΨF.obj (dualizingComplex' ℓ F.F) ⟶ dualizingComplex' ℓ F'.F
  /-- the proper exchange `χ_ι : Ψ_C Rι_* ⟶ Rι'_* Ψ_F`. -/
  χι : boundedConstructibleLowerStar ℓ F.ι ⋙ ΨC ⟶
    ΨF ⋙ boundedConstructibleLowerStar ℓ F'.ι
  /-- the proper exchange `χ_Δ : Ψ_{X×X} RΔ_* ⟶ RΔ'_* Ψ_X`. -/
  χΔ : boundedConstructibleLowerStar ℓ (diag X) ⋙ ΨXX ⟶
    ΨX ⋙ boundedConstructibleLowerStar ℓ (diag X')
  /-- the exceptional exchange `β_c : Ψ_C Rc^! ⟶ Rc'^! Ψ_{X×X}` of the support maps. -/
  βc : boundedConstructibleUpperShriek ℓ c.support ⋙ ΨC ⟶
    ΨXX ⋙ boundedConstructibleUpperShriek ℓ c'.support
  /-- the exceptional exchange `β_d : Ψ_F Rd^! ⟶ Rd'^! Ψ_X`. -/
  βd : boundedConstructibleUpperShriek ℓ F.d ⋙ ΨF ⟶
    ΨX ⋙ boundedConstructibleUpperShriek ℓ F'.d
  /-- the unit identity `χ_ι Ψ_C(η_ι) σ_C = Rι'_*(σ_F) η_ι'` (blueprint
  `proposition-specialization-trace-class`), read through the unit isomorphisms `Lι^* ℚ̄_ℓ ≅ ℚ̄_ℓ`
  of the monoidal pullbacks. -/
  unit_comp : σC ≫ ΨC.map ((boundedConstructibleUpperStarLowerStarAdjunction ℓ F.ι).unit.app
      (𝟙_ _)) ≫ χι.app _ =
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ F'.ι).unit.app (𝟙_ _) ≫
      (boundedConstructibleLowerStar ℓ F'.ι).map
        ((Functor.Monoidal.εIso
          (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ F'.ι)).inv ≫ σF ≫
          ΨF.map (Functor.Monoidal.εIso
            (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ F.ι)).hom)
  θF_eq : θF = ΨF.map (dualizingComplexComp ℓ F.d).inv ≫ βd.app (dualizingComplex' ℓ X) ≫
    (boundedConstructibleUpperShriek ℓ F'.d).map θX ≫
    (dualizingComplexComp ℓ F'.d).hom
  /-- the fixed-square identity `Rι'_* β_d ∘ χ_ι ∘ Ψ_C(B) = B' ∘ Rc'^!(χ_Δ) ∘ β_c(RΔ_*)`. -/
  fixedSquare (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ΨC.map (F.upperShriekLowerStarIso.app M).hom ≫
        χι.app _ ≫ (boundedConstructibleLowerStar ℓ F'.ι).map
          (βd.app M) =
      βc.app _ ≫ (boundedConstructibleUpperShriek ℓ c'.support).map
          (χΔ.app M) ≫ (F'.upperShriekLowerStarIso.app (ΨX.obj M)).hom

variable {c'} in
/-- The exceptional pullback `Rc'^! (K' ⊠ D K')` of the universal kernel along the support of
`c'` vanishes as soon as the ordinary pullback `Lc₂'^* K'` does: by external duality
(`verdierDualityIso`) it is `RHom(Lc₂'^* K', Rc₁'^! K')`. -/
lemma isZero_upperShriek_externalProduct_of_isZero
    (h : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c'.c₂).obj K')) :
    IsZero ((boundedConstructibleUpperShriek ℓ c'.support).obj
      (externalProduct ℓ K' (verdierDual ℓ K'))) :=
  (isZero_ihom_obj_of_isZero h _).of_iso c'.verdierDualityIso.symm

namespace TraceSpecialization

variable {c F c' F'} (T : c.TraceSpecialization F c' F')

/-- The diagram chase behind `σF_comp_map_homEquiv_symm`, in an arbitrary category. -/
private lemma comp_eq_of_unit_comp {𝒞 : Type*} [Category 𝒞] {A₀ A₁ A₂ A₃ A₄ A₅ A₆ : 𝒞}
    (σ : A₀ ⟶ A₁) (u : A₁ ⟶ A₂) (m : A₂ ⟶ A₃) (χ : A₃ ⟶ A₄) (χ₀ : A₂ ⟶ A₅) (m' : A₅ ⟶ A₄)
    (u' : A₀ ⟶ A₆) (w : A₆ ⟶ A₅) (w' : A₆ ⟶ A₄) (hχ : m ≫ χ = χ₀ ≫ m')
    (hu : σ ≫ u ≫ χ₀ = u' ≫ w) (hw : w ≫ m' = w') :
    σ ≫ (u ≫ m) ≫ χ = u' ≫ w' := by
  rw [Category.assoc, hχ, ← hw, reassoc_of% hu]

/-- The specialization units commute with the adjunctions `Lι^* ⊣ Rι_*`: for `g : Lι^* ℚ̄_ℓ ⟶ M`,
the specialization `σ_F Ψ_F(g)` is the `Lι'^* ⊣ Rι'_*` adjoint of the specialization
`χ_ι Ψ_C(g^♯) σ_C` of the adjoint `g^♯ : ℚ̄_ℓ ⟶ Rι_* M` of `g`. It follows from the unit identity
`unit_comp` and the naturality of `χ_ι`. -/
lemma σF_comp_map_eq_homEquiv_symm (M : Dᵇc(F.F.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (g : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ F.ι).obj (𝟙_ _) ⟶ M) :
    T.σF ≫ T.ΨF.map ((Functor.Monoidal.εIso
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ F.ι)).hom ≫ g) =
      (Functor.Monoidal.εIso
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ F'.ι)).hom ≫
        ((boundedConstructibleUpperStarLowerStarAdjunction ℓ F'.ι).homEquiv _ _).symm
          (T.σC ≫ T.ΨC.map
            (((boundedConstructibleUpperStarLowerStarAdjunction ℓ F.ι).homEquiv _ _) g) ≫
            T.χι.app M) := by
  have key : T.σC ≫ T.ΨC.map
      (((boundedConstructibleUpperStarLowerStarAdjunction ℓ F.ι).homEquiv _ _) g) ≫
        T.χι.app M =
      ((boundedConstructibleUpperStarLowerStarAdjunction ℓ F'.ι).homEquiv _ _)
        ((Functor.Monoidal.εIso
          (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ F'.ι)).inv ≫ T.σF ≫
          T.ΨF.map ((Functor.Monoidal.εIso
            (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ F.ι)).hom ≫ g)) := by
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, T.ΨC.map_comp]
    exact comp_eq_of_unit_comp _ _ _ _ _ _ _ _ _ (T.χι.naturality g) T.unit_comp
      (((boundedConstructibleLowerStar ℓ F'.ι).map_comp _
        _).symm.trans (congrArg _ (by rw [T.ΨF.map_comp]; simp only [Category.assoc])))
  rw [key, Equiv.symm_apply_apply, (Functor.Monoidal.εIso _).hom_inv_id_assoc]

/-- The *specialization* `sp_F(z) = θ_F Ψ_F(z) σ_F` of a Borel–Moore section `z` of the fixed
locus (blueprint `proposition-specialization-trace-class`). -/
noncomputable def sp (z : BorelMooreSection ℓ F.F) : BorelMooreSection ℓ F'.F :=
  T.σF ≫ T.ΨF.map z ≫ T.θF

/-- The specialization of the trace class is the `Lι'^* ⊣ Rι'_*` adjoint of the specialization
`χ_ι Ψ_C(𝔱 ũ) σ_C` of the composite of the mate `ũ` of `u` and the trace map `𝔱`, followed by
`Rι'_* θ_F`. -/
lemma sp_traceClass : T.sp (c.traceClass F) =
    (Functor.Monoidal.εIso
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ F'.ι)).hom ≫
      ((boundedConstructibleUpperStarLowerStarAdjunction ℓ F'.ι).homEquiv _ _).symm
        (T.σC ≫ T.ΨC.map c.mate ≫ T.ΨC.map (c.traceMap F) ≫ T.χι.app _ ≫
          (boundedConstructibleLowerStar ℓ F'.ι).map T.θF) := by
  have h1 := T.σF_comp_map_eq_homEquiv_symm (dualizingComplex' ℓ F.F)
    (((boundedConstructibleUpperStarLowerStarAdjunction ℓ F.ι).homEquiv _ _).symm
      (c.mate ≫ c.traceMap F))
  rw [Equiv.apply_symm_apply] at h1
  have h2 :=
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ F'.ι).homEquiv_naturality_right_symm
    (T.σC ≫ T.ΨC.map (c.mate ≫ c.traceMap F) ≫ T.χι.app _) T.θF
  calc T.sp (c.traceClass F)
      _ = (T.σF ≫ T.ΨF.map ((Functor.Monoidal.εIso
          (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ F.ι)).hom ≫
          ((boundedConstructibleUpperStarLowerStarAdjunction ℓ F.ι).homEquiv _ _).symm
            (c.mate ≫ c.traceMap F))) ≫ T.θF := (Category.assoc _ _ _).symm
      _ = _ := by rw [h1, Category.assoc, ← h2, Functor.map_comp]; simp only [Category.assoc]

/-- The diagram chase behind `map_traceKernel_specialization`, in an arbitrary category. -/
private lemma comp_eq_of_fixedSquare {𝒞 : Type*} [Category 𝒞]
    {A₀ A₁ A₂ A₃ A₄ A₅ A₆ A₇ A₈ A₉ A₁₀ : 𝒞} (a : A₀ ⟶ A₁) (b : A₁ ⟶ A₂) (x : A₂ ⟶ A₃)
    (χ₁ : A₃ ⟶ A₄) (t : A₄ ⟶ A₅) (χ₀ : A₂ ⟶ A₆) (y : A₆ ⟶ A₄) (z : A₆ ⟶ A₇) (w : A₇ ⟶ A₅)
    (β₀ : A₀ ⟶ A₈) (m : A₈ ⟶ A₉) (β₁ : A₁ ⟶ A₉) (n : A₉ ⟶ A₁₀) (b' : A₁₀ ⟶ A₇)
    (hχ : x ≫ χ₁ = χ₀ ≫ y) (hθ : y ≫ t = z ≫ w) (hβ : a ≫ β₁ = β₀ ≫ m)
    (hsq : b ≫ χ₀ ≫ z = β₁ ≫ n ≫ b') :
    a ≫ b ≫ x ≫ χ₁ ≫ t = β₀ ≫ m ≫ n ≫ b' ≫ w := by
  rw [reassoc_of% hχ, hθ, reassoc_of% hsq, reassoc_of% hβ]

/-- The specialization of the composite `Rc^! e ∘ B ∘ Rι_*(θ'_d)` of the exceptional pullback of a
map `e : P ⟶ RΔ_* ω_X`, the fixed-square base change and the composition isomorphism of the
dualizing complexes factors through `β_c(P)`. This is the formal part of
`traceMap_specialization`, for an arbitrary `e`. -/
theorem map_traceKernel_specialization {P : Dᵇc((X ⨯ X).left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (e : P ⟶ (boundedConstructibleLowerStar ℓ (diag X)).obj
      (dualizingComplex' ℓ X)) :
    T.ΨC.map ((boundedConstructibleUpperShriek ℓ c.support).map e)
        ≫ T.ΨC.map (F.upperShriekLowerStarIso.app (dualizingComplex' ℓ X)).hom ≫
        T.ΨC.map ((boundedConstructibleLowerStar ℓ F.ι).map
          (dualizingComplexComp ℓ F.d).hom) ≫ T.χι.app _ ≫
        (boundedConstructibleLowerStar ℓ F'.ι).map T.θF =
      T.βc.app P ≫
        (boundedConstructibleUpperShriek ℓ c'.support).map
          (T.ΨXX.map e) ≫
        (boundedConstructibleUpperShriek ℓ c'.support).map
          (T.χΔ.app _) ≫
        (F'.upperShriekLowerStarIso.app (T.ΨX.obj (dualizingComplex' ℓ X))).hom ≫
        (boundedConstructibleLowerStar ℓ F'.ι).map
          ((boundedConstructibleUpperShriek ℓ F'.d).map T.θX ≫
            (dualizingComplexComp ℓ F'.d).hom) := by
  have hχ : T.ΨC.map ((boundedConstructibleLowerStar ℓ F.ι).map
        (dualizingComplexComp ℓ F.d).hom) ≫ T.χι.app _ =
      T.χι.app _ ≫ (boundedConstructibleLowerStar ℓ F'.ι).map
        (T.ΨF.map (dualizingComplexComp ℓ F.d).hom) :=
    T.χι.naturality (dualizingComplexComp ℓ F.d).hom
  have hθ : T.ΨF.map (dualizingComplexComp ℓ F.d).hom ≫ T.θF =
      T.βd.app (dualizingComplex' ℓ X) ≫
        ((boundedConstructibleUpperShriek ℓ F'.d).map T.θX ≫
        (dualizingComplexComp ℓ F'.d).hom) := by
    rw [T.θF_eq, ← T.ΨF.map_comp_assoc, Iso.hom_inv_id, T.ΨF.map_id, Category.id_comp]
  have hθ' := ((boundedConstructibleLowerStar ℓ F'.ι).map_comp
      _ _).symm.trans ((congrArg
        (boundedConstructibleLowerStar ℓ F'.ι).map hθ).trans
      ((boundedConstructibleLowerStar ℓ F'.ι).map_comp _ _))
  exact comp_eq_of_fixedSquare _ _ _ _ _ _ _ _ _ _ _ _ _ _ hχ hθ' (T.βc.naturality e)
    (T.fixedSquare (dualizingComplex' ℓ X))

/-- **Specialization of the trace map** (blueprint `proposition-specialization-trace-class`, first
identity, with the nearby cycles of the universal kernel left unidentified): the specialized trace
map `Rι'_* θ_F ∘ χ_ι ∘ Ψ_C(𝔱)` factors through the exceptional exchange `β_c` at the universal
kernel `P = K ⊠ D_X K`:
```
Rι'_* θ_F ∘ χ_ι ∘ Ψ_C(𝔱) = Rι'_*(θ'_d ∘ Rd'^! θ_X) ∘ B' ∘ Rc'^!(χ_Δ ∘ Ψ_{X×X}(e_K)) ∘ β_c(P)
                              ∘ Ψ_C(λ),
```
where `λ : 𝓗_c(K) ≅ Rc^! P` is the external duality isomorphism and `e_K` the evaluation kernel.
It follows from the composition law for `θ`, the fixed-square identity and the naturality of
`χ_ι` and `β_c` (`map_traceKernel_specialization`). -/
theorem traceMap_specialization :
    T.ΨC.map (c.traceMap F) ≫ T.χι.app _ ≫
        (boundedConstructibleLowerStar ℓ F'.ι).map T.θF =
      T.ΨC.map c.verdierDualityIso.hom ≫ T.βc.app _ ≫
        (boundedConstructibleUpperShriek ℓ c'.support).map
          (T.ΨXX.map (evaluationKernel ℓ K)) ≫
        (boundedConstructibleUpperShriek ℓ c'.support).map
          (T.χΔ.app _) ≫
        (F'.upperShriekLowerStarIso.app (T.ΨX.obj (dualizingComplex' ℓ X))).hom ≫
        (boundedConstructibleLowerStar ℓ F'.ι).map
          ((boundedConstructibleUpperShriek ℓ F'.d).map T.θX ≫
            (dualizingComplexComp ℓ F'.d).hom) := by
  rw [← T.map_traceKernel_specialization (evaluationKernel ℓ K)]
  simp only [traceMap, Functor.map_comp, Category.assoc]

/-- **Vanishing of the specialized trace class**: if the exceptional pullback
`Rc'^! Ψ_{X×X}(K ⊠ D_X K)` of the specialized universal kernel vanishes, then the specialization
of the trace class of `u` vanishes, whatever the coefficient map `u`. This is the mechanism of
Varshavsky's vanishing argument (blueprint `theorem-contracting-correspondences-local-terms`). -/
theorem sp_traceClass_eq_zero
    (h : IsZero ((boundedConstructibleUpperShriek ℓ c'.support).obj
      (T.ΨXX.obj (externalProduct ℓ K (verdierDual ℓ K))))) :
    T.sp (c.traceClass F) = 0 := by
  have : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ F'.ι).IsLeftAdjoint :=
    ⟨_, ⟨boundedConstructibleUpperStarLowerStarAdjunction ℓ F'.ι⟩⟩
  have : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      F'.ι).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  rw [sp_traceClass, T.traceMap_specialization, h.eq_of_tgt
    (T.βc.app (externalProduct ℓ K (verdierDual ℓ K))) 0, zero_comp,
    comp_zero, comp_zero, comp_zero, Adjunction.homEquiv_counit, Functor.map_zero, zero_comp,
    comp_zero]

end TraceSpecialization

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
