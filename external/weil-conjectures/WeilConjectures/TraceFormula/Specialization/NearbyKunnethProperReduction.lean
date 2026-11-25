/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.Affine
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethClosure
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethGlobal
public import WeilConjectures.TraceFormula.Specialization.TraitModelRestrict
public import WeilConjectures.TraceFormula.Specialization.TraitProductRestrict
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethProper

/-!

# Gabber's Künneth formula for nearby cycles: reduction to proper models

Let `P` be the product over the strictly henselian trait `S = Spec k'⟦t⟧` of models `M`, `N`.
If the Künneth map `Π_{A,B} : Ψ_M A ⊠ Ψ_N B ⟶ Ψ_P (A ⊠ B)` is an isomorphism for all products
over the trait of models of finite type along proper structure morphisms, it is an isomorphism
for all products over the trait (`NearbyCyclesModel.isIso_kunnethMap_of_forall_isProper`).
Locality on the special fibre reduces to affine total spaces, and for affine total spaces one
passes to the models of the total spaces and to proper closures
(`NearbyCyclesModel.exists_isProper_openImmersion_of_isAffine`), extending the coefficients by
zero (`NearbyCyclesModel.isIso_kunnethMap_of_forall_isProper_of_isAffine`,
`WeilConjectures.TraceFormula.Specialization.NearbyKunnethClosure`). The proper case is
`WeilConjectures.TraceFormula.Specialization.NearbyKunnethProper`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime]

namespace NearbyCyclesModel

variable {k' : Type u} [Field k'] [IsSepClosed k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)] {X Y Z : Scheme.{u}} {X' Y' Z' : Over (Spec (.of k'))}
  {M : NearbyCyclesModel X X'.left} {N : NearbyCyclesModel Y Y'.left}
  {P : NearbyCyclesModel Z Z'.left} {f₁ : Z ⟶ X} {f₁' : Z'.left ⟶ X'.left} {f₂ : Z ⟶ Y}
  {f₂' : Z'.left ⟶ Y'.left} {φ₁ : P.Hom M f₁ f₁'} {φ₂ : P.Hom N f₂ f₂'}
  {qM : M.total ⟶ trait k'} {gM : M.generic ⟶ Spec (.of (traitGenericField k'))}
  {qN : N.total ⟶ trait k'} {gN : N.generic ⟶ Spec (.of (traitGenericField k'))}

omit [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] in
/-- The Künneth formula for products over the trait of proper models with compatible projections
applies to the product `X̄ ×_S Ȳ` of the standard models of proper schemes over the trait. -/
theorem isIso_kunnethMap_closure_of_forall_isProper
    (hproper : ∀ {X Y Z : Scheme.{u}} {X' Y' Z' : Over (Spec (.of k'))}
      {M : NearbyCyclesModel X X'.left} {N : NearbyCyclesModel Y Y'.left}
      {P : NearbyCyclesModel Z Z'.left} {f₁ : Z ⟶ X} {f₁' : Z'.left ⟶ X'.left} {f₂ : Z ⟶ Y}
      {f₂' : Z'.left ⟶ Y'.left} (φ₁ : P.Hom M f₁ f₁') (φ₂ : P.Hom N f₂ f₂')
      {qM : M.total ⟶ trait k'} {gM : M.generic ⟶ Spec (.of (traitGenericField k'))}
      {qN : N.total ⟶ trait k'} {gN : N.generic ⟶ Spec (.of (traitGenericField k'))},
      M.IsTraitModelOver qM gM → N.IsTraitModelOver qN gN →
      IsPullback φ₁.total φ₂.total qM qN →
      P.IsTraitModelOver (φ₁.total ≫ qM) (φ₁.generic ≫ gM) →
      φ₂.generic ≫ gN = φ₁.generic ≫ gM → IsProper qM → IsProper qN →
      ∀ {eM : M.total ⟶ X}, M.j ≫ eM = M.ε → ∀ {eN : N.total ⟶ Y}, N.j ≫ eN = N.ε →
      ∀ {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))}
        {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
          (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y))},
        boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) A →
          boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y) B → IsIso
              (kunnethMap (Profinite.padicAlgClRingObj ℓ) φ₁ φ₂ A B))
    {Xc Yc : Scheme.{u}} (qcM : Xc ⟶ trait k') (qcN : Yc ⟶ trait k') [IsProper qcM]
    [IsProper qcN]
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Xc) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Xc)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Yc) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Yc)))
    (hA : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Xc) A)
    (hB : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Yc) B) :
    IsIso (kunnethMap (Profinite.padicAlgClRingObj ℓ) (closureFst qcM qcN) (closureSnd qcM qcN) A B)
        := by
  refine hproper (closureFst qcM qcN) (closureSnd qcM qcN) (qM := qcM)
    (gM := pullback.snd qcM (traitGenericPoint k')) (qN := qcN)
    (gN := pullback.snd qcN (traitGenericPoint k'))
    ⟨inferInstance, inferInstance, inferInstance, IsPullback.of_hasPullback _ _,
      IsPullback.of_hasPullback _ _⟩
    ⟨inferInstance, inferInstance, inferInstance, IsPullback.of_hasPullback _ _,
      IsPullback.of_hasPullback _ _⟩
    (IsPullback.of_hasPullback qcM qcN)
    ⟨inferInstanceAs (LocallyOfFiniteType (pullback.fst qcM qcN ≫ qcM)),
      inferInstanceAs (QuasiCompact (pullback.fst qcM qcN ≫ qcM)),
      inferInstanceAs (IsSeparated (pullback.fst qcM qcN ≫ qcM)), ?_,
      IsPullback.of_hasPullback _ _⟩
    (by simp) inferInstance inferInstance (eM := 𝟙 _) (by simp [geometric]) (eN := 𝟙 _)
    (by simp [geometric]) hA hB
  have e : (closureFst qcM qcN).generic ≫ pullback.snd qcM (traitGenericPoint k') =
      pullback.snd (pullback.fst qcM qcN ≫ qcM) (traitGenericPoint k') := by simp
  rw [e]
  exact IsPullback.of_hasPullback _ _

omit [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] in
/-- **Reduction of Gabber's Künneth formula to proper models, affine case** (blueprint
`proposition-external-kunneth-formula-nearby-cycles`, "Reduction to projective flat families";
Illusie,
*Autour du théorème de monodromie locale*, proof of Thm. 4.7): if the Künneth map is an isomorphism
for all products over the trait of models of finite type along proper structure morphisms, with
projections compatible with the structure morphisms of the geometric generic fibres to `Spec Ω`,
then it is an isomorphism for products over the trait of models with affine total spaces.

The Künneth map is that of the models of the total spaces
(`NearbyCyclesModel.isIso_kunnethMap_of_toGeometricGeneric`); these are restrictions of the
standard models of projective closures of the total spaces
(`NearbyCyclesModel.exists_isProper_openImmersion_of_isAffine`), and the coefficients are
extended by zero (`NearbyCyclesModel.isIso_kunnethMap_toGeometricGeneric_of_closure`). -/
theorem isIso_kunnethMap_of_forall_isProper_of_isAffine
    (hproper : ∀ {X Y Z : Scheme.{u}} {X' Y' Z' : Over (Spec (.of k'))}
      {M : NearbyCyclesModel X X'.left} {N : NearbyCyclesModel Y Y'.left}
      {P : NearbyCyclesModel Z Z'.left} {f₁ : Z ⟶ X} {f₁' : Z'.left ⟶ X'.left} {f₂ : Z ⟶ Y}
      {f₂' : Z'.left ⟶ Y'.left} (φ₁ : P.Hom M f₁ f₁') (φ₂ : P.Hom N f₂ f₂')
      {qM : M.total ⟶ trait k'} {gM : M.generic ⟶ Spec (.of (traitGenericField k'))}
      {qN : N.total ⟶ trait k'} {gN : N.generic ⟶ Spec (.of (traitGenericField k'))},
      M.IsTraitModelOver qM gM → N.IsTraitModelOver qN gN →
      IsPullback φ₁.total φ₂.total qM qN →
      P.IsTraitModelOver (φ₁.total ≫ qM) (φ₁.generic ≫ gM) →
      φ₂.generic ≫ gN = φ₁.generic ≫ gM → IsProper qM → IsProper qN →
      ∀ {eM : M.total ⟶ X}, M.j ≫ eM = M.ε → ∀ {eN : N.total ⟶ Y}, N.j ≫ eN = N.ε →
      ∀ {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))}
        {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
          (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y))},
        boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) A →
          boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y) B → IsIso
              (kunnethMap (Profinite.padicAlgClRingObj ℓ) φ₁ φ₂ A B))
    (h : IsTraitProduct φ₁ φ₂) (hMa : IsAffine M.total) (hNa : IsAffine N.total)
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))}
    (hA : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) A)
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y))}
    (hB : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y) B) :
    IsIso (kunnethMap (Profinite.padicAlgClRingObj ℓ) φ₁ φ₂ A B) := by
  obtain ⟨qM, gM, qN, gN, hM, hN, hpb, hP, hc⟩ := h.exists_isTraitModelOver
  obtain ⟨eM, heM⟩ := h.exists_comp_ε_left
  obtain ⟨eN, heN⟩ := h.exists_comp_ε_right
  have := hMa
  have := hNa
  have := hM.locallyOfFiniteType
  have := hN.locallyOfFiniteType
  obtain ⟨Xc, qcM, uM, hqM, huM, hcM⟩ := exists_isProper_openImmersion_of_isAffine qM
  obtain ⟨Yc, qcN, uN, hqN, huN, hcN⟩ := exists_isProper_openImmersion_of_isAffine qN
  have := noetherianSpace_of_isProper qcM
  have := noetherianSpace_of_isProper qcN
  refine isIso_kunnethMap_of_toGeometricGeneric (Profinite.padicAlgClRingObj ℓ) _ _ heM heN A B ?_
  exact isIso_kunnethMap_toGeometricGeneric_of_closure (Profinite.padicAlgClRingObj ℓ) hM hN hpb hP
      hc uM uN hcM hcN
    (fun A' B' hA' hB' ↦ isIso_kunnethMap_closure_of_forall_isProper
        hproper qcM qcN A' B' hA'
      hB')
    (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ _ _ hA)
    (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ _ _ hB)

omit [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] in
/-- **Reduction of Gabber's Künneth formula to proper models** (blueprint
`proposition-external-kunneth-formula-nearby-cycles`, "Reduction to projective flat families";
Illusie,
*Autour du théorème de monodromie locale*, proof of Thm. 4.7): if the Künneth map is an isomorphism
for all products over the trait of models of finite type along proper structure morphisms, with
projections compatible with the structure morphisms of the geometric generic fibres to `Spec Ω`,
then it is an isomorphism for all products over the trait.

The assertion is local on the special fibre
(`NearbyCyclesModel.isIso_kunnethMap_of_forall_exists_restriction`): around each point of the
special fibre the product restricts to the product `V ×_S W` of affine opens `V`, `W` of the total
spaces (`NearbyCyclesModel.IsTraitProduct.restrictOpen`), where
`NearbyCyclesModel.isIso_kunnethMap_of_forall_isProper_of_isAffine` applies. -/
theorem isIso_kunnethMap_of_forall_isProper
    (hproper : ∀ {X Y Z : Scheme.{u}} {X' Y' Z' : Over (Spec (.of k'))}
      {M : NearbyCyclesModel X X'.left} {N : NearbyCyclesModel Y Y'.left}
      {P : NearbyCyclesModel Z Z'.left} {f₁ : Z ⟶ X} {f₁' : Z'.left ⟶ X'.left} {f₂ : Z ⟶ Y}
      {f₂' : Z'.left ⟶ Y'.left} (φ₁ : P.Hom M f₁ f₁') (φ₂ : P.Hom N f₂ f₂')
      {qM : M.total ⟶ trait k'} {gM : M.generic ⟶ Spec (.of (traitGenericField k'))}
      {qN : N.total ⟶ trait k'} {gN : N.generic ⟶ Spec (.of (traitGenericField k'))},
      M.IsTraitModelOver qM gM → N.IsTraitModelOver qN gN →
      IsPullback φ₁.total φ₂.total qM qN →
      P.IsTraitModelOver (φ₁.total ≫ qM) (φ₁.generic ≫ gM) →
      φ₂.generic ≫ gN = φ₁.generic ≫ gM → IsProper qM → IsProper qN →
      ∀ {eM : M.total ⟶ X}, M.j ≫ eM = M.ε → ∀ {eN : N.total ⟶ Y}, N.j ≫ eN = N.ε →
      ∀ {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))}
        {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
          (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y))},
        boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) A →
          boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y) B → IsIso
              (kunnethMap (Profinite.padicAlgClRingObj ℓ) φ₁ φ₂ A B))
    (h : IsTraitProduct φ₁ φ₂)
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))}
    (hA : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) A)
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y))}
    (hB : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y) B) :
    IsIso (kunnethMap (Profinite.padicAlgClRingObj ℓ) φ₁ φ₂ A B) := by
  obtain ⟨qM, gM, qN, gN, hM, hN, -, hP, -⟩ := h.exists_isTraitModelOver
  have := hM.isTraitModel.isNoetherian_total
  have := hN.isTraitModel.isNoetherian_total
  have := hP.isTraitModel.isNoetherian_total
  have : LocallyOfFiniteType Z'.hom :=
    MorphismProperty.of_isPullback hP.isPullback_i hP.locallyOfFiniteType
  have : QuasiCompact Z'.hom := MorphismProperty.of_isPullback hP.isPullback_i hP.quasiCompact
  have : IsLocallyNoetherian Z'.left := LocallyOfFiniteType.isLocallyNoetherian Z'.hom
  have : CompactSpace Z'.left := QuasiCompact.compactSpace_of_compactSpace Z'.hom
  have : IsNoetherian Z'.left := ⟨⟩
  refine isIso_kunnethMap_of_forall_exists_restriction (Profinite.padicAlgClRingObj ℓ) φ₁ φ₂ A B fun
      z ↦ ?_
  obtain ⟨V, hV, hzV, -⟩ := exists_isAffineOpen_mem_and_subset
    (x := φ₁.total (P.i z)) (U := ⊤) trivial
  obtain ⟨W, hW, hzW, -⟩ := exists_isAffineOpen_mem_and_subset
    (x := φ₂.total (P.i z)) (U := ⊤) trivial
  have hVq : QuasiCompact V.ι := inferInstance
  have hWq : QuasiCompact W.ι := inferInstance
  have hUq : QuasiCompact (productOpen φ₁ φ₂ V W).ι := inferInstance
  refine ⟨P.i ⁻¹ᵁ productOpen φ₁ φ₂ V W, _, _, _, _, _, M.restrictOpen V, N.restrictOpen W,
    P.restrictOpen (productOpen φ₁ φ₂ V W), f₁, _, f₂, _, 𝟙 X, _, 𝟙 Y, _, 𝟙 Z,
    φ₁.restrictOpen _ V inf_le_left, φ₂.restrictOpen _ W inf_le_right, M.restrictOpenHom V,
    N.restrictOpenHom W, P.restrictOpenHom _, ⟨hzV, hzW⟩,
    isKunnethRestriction_restrictOpen φ₁ φ₂ V W, ?_⟩
  exact isIso_kunnethMap_of_forall_isProper_of_isAffine hproper
      (h.restrictOpen V W) hV hW
    ((boundedConstructible _).prop_of_iso ((leftDerivedUpperStarId (Profinite.padicAlgClRingObj ℓ)
        X).app A).symm hA)
    ((boundedConstructible _).prop_of_iso ((leftDerivedUpperStarId (Profinite.padicAlgClRingObj ℓ)
        Y).app B).symm hB)

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
