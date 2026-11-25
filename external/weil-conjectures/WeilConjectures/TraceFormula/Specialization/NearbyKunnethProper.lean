/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Compactification.AffineCharts
public import WeilConjectures.TraceFormula.Specialization.ClosedPointsSupport
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethClosure
public import WeilConjectures.TraceFormula.Specialization.NearbyFiniteness
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethFiniteSupport
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethGlobal
public import WeilConjectures.TraceFormula.Specialization.TraitModelRestrict
public import WeilConjectures.TraceFormula.Specialization.TraitProductRestrict

/-!

# Gabber's Künneth formula for nearby cycles: proper models

Let `P` be the product over the strictly henselian trait `S = Spec k'⟦t⟧` (`k'` separably closed)
of models `M`, `N` of finite type along proper structure morphisms, with projections compatible
with the structure morphisms of the geometric generic fibres to `Spec Ω`. This file proves that
the Künneth map `Π_{A,B} : Ψ_M A ⊠ Ψ_N B ⟶ Ψ_P (A ⊠ B)` is an isomorphism
(`AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.isIso_kunnethMap_of_isProper`),
following Illusie's argument (*Autour du théorème de monodromie locale*, Thm. 4.7; blueprint
`proposition-external-kunneth-formula-nearby-cycles`): the cone `C` of `Π_{A,B}`

* has no global sections, `RΓ(X_s × Y_s, C) = 0` (the global-sections step,
  `NearbyCyclesModel.isIso_lowerStar_kunnethMap`);
* is supported on finitely many closed points
  (`NearbyCyclesModel.exists_finite_isIso_upperStar_map_kunnethMap`, the finite-support step);

and a bounded constructible complex supported on finitely many closed points without global
sections vanishes (blueprint `lemma-finite-support-global-sections--1`; for `ℚ̄_ℓ`-coefficients
`ProEtale.CondensedRing.isZero_of_isZero_upperStar_finsetComplOpens`).

The finite-support step is proved in chart dimension `n` (charts `V ⟶ 𝔸ᵐ_S` with `m` summed over
the two factors, `AlgebraicGeometry.Scheme.Hom.LocallyEmbedsInAffineSpace`), given the
generic-slicing step in chart dimension `n - 1` (`NearbyCyclesModel.SliceKunnethFormula`), which
is deduced from the Künneth formula over the trait `Spec K⟦t⟧` of the generic slices in
`WeilConjectures.TraceFormula.Specialization.NearbyKunnethIntegral`.

The reduction to proper models in chart dimension `n` (`NearbyCyclesModel.ProperKunnethFormula`)
is proved: locality on the special fibre reduces to products of charts
(`NearbyCyclesModel.isIso_kunnethMap_of_properKunnethFormula`), and for a chart one passes to the
models of the total spaces and to their closures in projective spaces, whose charts have the same
dimension, extending the coefficients by zero
(`NearbyCyclesModel.isIso_kunnethMap_of_properKunnethFormula_of_isImmersion`,
`WeilConjectures.TraceFormula.Specialization.NearbyKunnethClosure`).

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

omit [IsSepClosed k'] [Fact (ringChar k').Prime] in
/-- The source `Lf₁'^* Ψ_M A ⊗ Lf₂'^* Ψ_N B` of the Künneth map is bounded constructible if the
nearby cycles `Ψ_M A`, `Ψ_N B` are. -/
lemma boundedConstructible_kunnethMap_source
    [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom]
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))}
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y))}
    (hΨA : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X'.left)
        ((M.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj A))
    (hΨB : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y'.left)
        ((N.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj B)) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z'.left)
      (L((f₁')^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj ((M.nearbyCycles (Profinite.padicAlgClRingObj
          ℓ)).obj A) ⊗
        L((f₂')^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj ((N.nearbyCycles (Profinite.padicAlgClRingObj
            ℓ)).obj B)) := by
  have : (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
      Z'.left)).IsMonoidal :=
    isMonoidal_boundedConstructible (X := Z') (ℓ := ℓ)
  exact CategoryTheory.ObjectProperty.prop_tensor
    (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ _ _ hΨA)
    (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ _ _ hΨB)

-- instance search for the monoidal structure of bounded constructible complexes
omit [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] in
include φ₁ φ₂ in
/-- The target `Ψ_P (Lf₁^* A ⊗ Lf₂^* B)` of the Künneth map is bounded constructible if the
geometric nearby cycles `Li^* Rj_* Lj^*` of `P` preserve bounded constructible complexes: since
`ε_M` and `ε_N` factor through the total spaces, `Lε_P^* (Lf₁^* A ⊗ Lf₂^* B)` is the pullback
`Lj^* C₀` of a bounded constructible complex on the total space of `P`. -/
lemma boundedConstructible_kunnethMap_target (qP : P.total ⟶ trait k')
    [LocallyOfFiniteType qP] [QuasiCompact qP]
    (hgeom : ∀ C₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology P.total) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) P.total)), boundedConstructible
            (condensedRingObj (Profinite.padicAlgClRingObj ℓ) P.total) C₀ →
      boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z'.left)
          ((P.geometric.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj C₀))
    {eM : M.total ⟶ X} (heM : M.j ≫ eM = M.ε) {eN : N.total ⟶ Y} (heN : N.j ≫ eN = N.ε)
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))}
    (hA : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) A)
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y))}
    (hB : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y) B) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z'.left)
      ((P.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj (L((f₁)^*⟦Profinite.padicAlgClRingObj
          ℓ⟧).obj A ⊗ L((f₂)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj B)) := by
  have htensor : ∀ C D : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology P.total) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) P.total)), boundedConstructible
          (condensedRingObj (Profinite.padicAlgClRingObj ℓ) P.total) C →
        boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) P.total) D →
          boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) P.total) (C ⊗ D) :=
              by
    have : IsLocallyNoetherian P.total := LocallyOfFiniteType.isLocallyNoetherian qP
    have : CompactSpace P.total := QuasiCompact.compactSpace_of_compactSpace qP
    have : IsNoetherian P.total := {}
    exact fun C D hC hD ↦
      boundedConstructible_tensorObj
        (tensorHypotheses_padicAlgClRingObj ℓ).lisseTensorHypotheses hC hD
  obtain ⟨C₀, hC₀, ⟨e⟩⟩ := exists_boundedConstructible_tensor_iso (Profinite.padicAlgClRingObj ℓ) φ₁
      φ₂ heM heN hA hB htensor
  exact (boundedConstructible _).prop_of_iso (L((P.i)^*⟦Profinite.padicAlgClRingObj ℓ⟧).mapIso
      (R((P.j)_*⟦Profinite.padicAlgClRingObj ℓ⟧).mapIso
    ((Functor.Monoidal.μIso L((P.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧) _ _).symm ≪≫
      (((pullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) φ₁.commSq_ε).app A).symm ⊗ᵢ
        ((pullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) φ₂.commSq_ε).app B).symm) ≪≫
            e).symm)) (hgeom C₀ hC₀)

/-- **The finite-support step of Gabber's Künneth formula** (blueprint
`proposition-external-kunneth-formula-nearby-cycles`, "Finite support"; Illusie, *Autour du théorème
de monodromie locale*, proof of Thm. 4.7): for the product `P` over the strictly henselian trait of
models `M`, `N` of finite type and bounded constructible `A`, `B`, the Künneth map `Π_{A,B}` is an
isomorphism away from finitely many closed points of the special fibre `X_s × Y_s`, given that the
total spaces locally embed into `𝔸ᵐ_S`, `𝔸^{m'}_S` and that the generic-slicing step holds in
chart dimension `m + m' - 1` (`NearbyCyclesModel.SliceKunnethFormula`).

The source and target of `Π_{A,B}` are bounded constructible by Deligne's finiteness theorem
(`NearbyCyclesModel.preservesBoundedConstructible_of_isTraitModel`,
`NearbyCyclesModel.boundedConstructible_geometricNearbyCycles_obj`), so this is
`NearbyCyclesModel.exists_finite_isIso_upperStar_map_kunnethMap_of_boundedConstructible`: around
every point, the coordinates of local charts of the total spaces detect closed points of the
special fibre, and the cone of `Π_{A,B}` vanishes over the generic point of each coordinate line
by generic slicing (`NearbyCyclesModel.SliceKunnethFormula`). -/
theorem exists_finite_isIso_upperStar_map_kunnethMap [TopologicalSpace.NoetherianSpace X]
    [TopologicalSpace.NoetherianSpace Y] [TopologicalSpace.NoetherianSpace Z]
    (hM : M.IsTraitModelOver qM gM)
    (hN : N.IsTraitModelOver qN gN) (hpb : IsPullback φ₁.total φ₂.total qM qN)
    (hP : P.IsTraitModelOver (φ₁.total ≫ qM) (φ₁.generic ≫ gM))
    (hgen : φ₂.generic ≫ gN = φ₁.generic ≫ gM) {m m' : ℕ}
    (hm : qM.LocallyEmbedsInAffineSpace m) (hm' : qN.LocallyEmbedsInAffineSpace m')
    (hslice : 0 < m + m' → SliceKunnethFormula (Profinite.padicAlgClRingObj ℓ) k' (m + m' - 1))
    {eM : M.total ⟶ X} (heM : M.j ≫ eM = M.ε) {eN : N.total ⟶ Y} (heN : N.j ≫ eN = N.ε)
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))}
    (hA : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) A)
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y))}
    (hB : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y) B) :
    ∃ (S : Finset Z'.left) (hS : ∀ x ∈ S, IsClosed {x}),
      IsIso (L(((finsetComplOpens S hS).ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧).map (kunnethMap
          (Profinite.padicAlgClRingObj ℓ) φ₁ φ₂ A B)) := by
  have : LocallyOfFiniteType Z'.hom := MorphismProperty.of_isPullback hP.isPullback_i
    hP.locallyOfFiniteType
  have : QuasiCompact Z'.hom := MorphismProperty.of_isPullback hP.isPullback_i hP.quasiCompact
  have : IsSeparated Z'.hom := MorphismProperty.of_isPullback hP.isPullback_i hP.isSeparated
  have hΨA := preservesBoundedConstructible_of_isTraitModel M hM.isTraitModel ⟨eM, heM⟩ A hA
  have := hP.locallyOfFiniteType
  have := hP.quasiCompact
  have hΨB := preservesBoundedConstructible_of_isTraitModel N hN.isTraitModel ⟨eN, heN⟩ B hB
  exact exists_finite_isIso_upperStar_map_kunnethMap_of_boundedConstructible hM hN hpb hP hgen hm
    hm' hslice heM heN
    hA hB (boundedConstructible_kunnethMap_source hΨA hΨB)
    (boundedConstructible_kunnethMap_target (φ₁ := φ₁) (φ₂ := φ₂) (φ₁.total ≫ qM)
      (fun C₀ hC₀ ↦ boundedConstructible_geometricNearbyCycles_obj P hP.isTraitModel hC₀)
      heM heN hA hB)

private lemma finiteSupport_and_lowerStar_kunnethMap [TopologicalSpace.NoetherianSpace X]
    [TopologicalSpace.NoetherianSpace Y] [TopologicalSpace.NoetherianSpace Z]
    (hM : M.IsTraitModelOver qM gM)
    (hN : N.IsTraitModelOver qN gN) (hpb : IsPullback φ₁.total φ₂.total qM qN)
    (hP : P.IsTraitModelOver (φ₁.total ≫ qM) (φ₁.generic ≫ gM))
    (hgen : φ₂.generic ≫ gN = φ₁.generic ≫ gM) [IsProper qM] [IsProper qN]
    {m m' : ℕ} (hm : qM.LocallyEmbedsInAffineSpace m) (hm' : qN.LocallyEmbedsInAffineSpace m')
    (hslice : 0 < m + m' → SliceKunnethFormula (Profinite.padicAlgClRingObj ℓ) k' (m + m' - 1))
    {eM : M.total ⟶ X} (heM : M.j ≫ eM = M.ε) {eN : N.total ⟶ Y} (heN : N.j ≫ eN = N.ε)
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))}
    (hA : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) A)
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y))}
    (hB : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y) B)
    (hΨA : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X'.left)
        ((M.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj A))
    (hΨB : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y'.left)
        ((N.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj B))
    (hT : IsIso (kunnethMap (Profinite.padicAlgClRingObj ℓ) (Hom.id (traitGenericModel k'))
      (Hom.id (traitGenericModel k'))
      (R((gM)_*⟦Profinite.padicAlgClRingObj ℓ⟧).obj
        (L((M.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj A))
      (R((gN)_*⟦Profinite.padicAlgClRingObj ℓ⟧).obj
        (L((N.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj B)))) :
    ∃ (S : Finset Z'.left) (hS : ∀ x ∈ S, IsClosed {x}),
      IsIso (R((Z'.hom)_*⟦Profinite.padicAlgClRingObj ℓ⟧).map
        (kunnethMap (Profinite.padicAlgClRingObj ℓ) φ₁ φ₂ A B)) ∧
      IsIso (L(((finsetComplOpens S hS).ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧).map
        (kunnethMap (Profinite.padicAlgClRingObj ℓ) φ₁ φ₂ A B)) := by
  obtain ⟨S, hS, hU⟩ := exists_finite_isIso_upperStar_map_kunnethMap
    hM hN hpb hP hgen hm hm' hslice heM heN hA hB
  have hR := isIso_lowerStar_kunnethMap hM hN hpb hP hgen heM heN hA hB hΨA hΨB hT
  exact ⟨S, hS, hR, hU⟩

omit [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] in
private lemma isIso_of_isIso_upperStar_and_lowerStar
    [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]
    {K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z'.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z'.left))}
    (f : K ⟶ L)
    (hsrc : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z'.left) K)
    (htgt : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z'.left) L)
    (hdetect : ∀ (S : Finset Z'.left) (hS : ∀ x ∈ S, IsClosed {x})
      (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z'.left) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z'.left))),
      boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z'.left) C →
        IsZero (L(((finsetComplOpens S hS).ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C) →
          IsZero (R((Z'.hom)_*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C) → IsZero C)
    (S : Finset Z'.left) (hS : ∀ x ∈ S, IsClosed {x})
    (hU : IsIso (L(((finsetComplOpens S hS).ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧).map f))
    (hR : IsIso (R((Z'.hom)_*⟦Profinite.padicAlgClRingObj ℓ⟧).map f)) : IsIso f := by
  obtain ⟨C, g, δ, hT⟩ := distinguished_cocone_triangle f
  have : IsLocallyNoetherian Z'.left := LocallyOfFiniteType.isLocallyNoetherian Z'.hom
  have : CompactSpace Z'.left := QuasiCompact.compactSpace_of_compactSpace Z'.hom
  have : IsNoetherian Z'.left := ⟨⟩
  have hC := (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
      Z'.left)).ext_of_isTriangulatedClosed₃ _ hT hsrc htgt
  have h₁ := Triangle.isZero₃_of_isIso₁ _
    (R((Z'.hom)_*⟦Profinite.padicAlgClRingObj ℓ⟧).map_distinguished _ hT) hR
  have h₂ := Triangle.isZero₃_of_isIso₁ _
    (L(((finsetComplOpens S hS).ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧).map_distinguished _ hT) hU
  exact (Triangle.isZero₃_iff_isIso₁ _ hT).1
    (hdetect S hS C hC h₂ h₁)

-- the triangle of the Künneth map has large terms
/-- **Gabber's Künneth formula for proper models** (Illusie, *Autour du théorème de monodromie
locale*, Thm. 4.7; blueprint `proposition-external-kunneth-formula-nearby-cycles`): for the product
`P` over the strictly henselian trait of models `M`, `N` of finite type along proper structure
morphisms, with projections compatible with the structure morphisms to `Spec Ω`, and bounded
constructible `A`, `B`, the Künneth map `Π_{A,B}` is an isomorphism. Its cone `C` is bounded
constructible (given that the source and target of `Π_{A,B}` are, by Deligne's finiteness theorem),
has no global sections (`NearbyCyclesModel.isIso_lowerStar_kunnethMap`, given that the Künneth map
of the trait at the cohomology of the geometric generic fibres is invertible), and is supported on
finitely many closed points (`NearbyCyclesModel.exists_finite_isIso_upperStar_map_kunnethMap`);
hence it vanishes (the hypothesis `hdetect`, blueprint
`lemma-finite-support-global-sections--1`). -/
theorem isIso_kunnethMap_of_isProper [TopologicalSpace.NoetherianSpace X]
    [TopologicalSpace.NoetherianSpace Y] [TopologicalSpace.NoetherianSpace Z]
    (hM : M.IsTraitModelOver qM gM)
    (hN : N.IsTraitModelOver qN gN) (hpb : IsPullback φ₁.total φ₂.total qM qN)
    (hP : P.IsTraitModelOver (φ₁.total ≫ qM) (φ₁.generic ≫ gM))
    (hgen : φ₂.generic ≫ gN = φ₁.generic ≫ gM) [IsProper qM] [IsProper qN]
    {m m' : ℕ} (hm : qM.LocallyEmbedsInAffineSpace m) (hm' : qN.LocallyEmbedsInAffineSpace m')
    (hslice : 0 < m + m' → SliceKunnethFormula (Profinite.padicAlgClRingObj ℓ) k' (m + m' - 1))
    {eM : M.total ⟶ X} (heM : M.j ≫ eM = M.ε) {eN : N.total ⟶ Y} (heN : N.j ≫ eN = N.ε)
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))}
    (hA : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) A)
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y))}
    (hB : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y) B)
    (hΨA : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X'.left)
        ((M.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj A))
    (hΨB : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y'.left)
        ((N.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj B))
    (hsrc : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z'.left)
      (L((f₁')^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj ((M.nearbyCycles (Profinite.padicAlgClRingObj
          ℓ)).obj A) ⊗
        L((f₂')^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj ((N.nearbyCycles (Profinite.padicAlgClRingObj
            ℓ)).obj B)))
    (htgt : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z'.left)
      ((P.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj (L((f₁)^*⟦Profinite.padicAlgClRingObj
          ℓ⟧).obj A ⊗ L((f₂)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj B)))
    (hT : IsIso (kunnethMap (Profinite.padicAlgClRingObj ℓ) (Hom.id (traitGenericModel k')) (Hom.id
        (traitGenericModel k'))
      (R((gM)_*⟦Profinite.padicAlgClRingObj ℓ⟧).obj (L((M.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj
          A)) (R((gN)_*⟦Profinite.padicAlgClRingObj ℓ⟧).obj (L((N.ε)^*⟦Profinite.padicAlgClRingObj
              ℓ⟧).obj B))))
    (hdetect : ∀ (S : Finset Z'.left) (hS : ∀ x ∈ S, IsClosed {x})
      (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z'.left) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z'.left))), boundedConstructible
            (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z'.left) C →
      IsZero (L(((finsetComplOpens S hS).ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C) →
        IsZero (R((Z'.hom)_*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C) → IsZero C) :
    IsIso (kunnethMap (Profinite.padicAlgClRingObj ℓ) φ₁ φ₂ A B) := by
  obtain ⟨S, hS, hR, hU⟩ := finiteSupport_and_lowerStar_kunnethMap
    hM hN hpb hP hgen hm hm' hslice heM heN hA hB hΨA hΨB hT
  have : LocallyOfFiniteType Z'.hom := MorphismProperty.of_isPullback hP.isPullback_i
    hP.locallyOfFiniteType
  have : QuasiCompact Z'.hom := MorphismProperty.of_isPullback hP.isPullback_i hP.quasiCompact
  have : IsSeparated Z'.hom := MorphismProperty.of_isPullback hP.isPullback_i hP.isSeparated
  exact isIso_of_isIso_upperStar_and_lowerStar
    (kunnethMap (Profinite.padicAlgClRingObj ℓ) φ₁ φ₂ A B) hsrc htgt hdetect S hS hU hR

omit [IsSepClosed k'] [Fact (ringChar k').Prime] in
/-- **Projective closures over the trait**: an affine scheme of finite type over the trait
`S = Spec k'⟦t⟧` is an open subscheme of a proper `S`-scheme: its closure in `ℙⁿ_S` along an
immersion into `𝔸ⁿ_S ⊆ ℙⁿ_S` (`AlgebraicGeometry.HasCompactification.of_isQuasiAffine`). -/
theorem exists_isProper_openImmersion_of_isAffine {T : Scheme.{u}} (q : T ⟶ trait k')
    [IsAffine T] [LocallyOfFiniteType q] :
    ∃ (Tc : Scheme.{u}) (qc : Tc ⟶ trait k') (c : T ⟶ Tc), IsProper qc ∧ IsOpenImmersion c ∧
      c ≫ qc = q := by
  have : QuasiCompact q := inferInstance
  have := HasCompactification.of_isQuasiAffine q
  let c := HasCompactification.compactification q
  exact ⟨c.Z, c.g, c.i, c.isProper, c.isOpenImmersion, c.comm.symm⟩

omit [IsSepClosed k'] [Fact (ringChar k').Prime] in
/-- A proper scheme over the trait is noetherian. -/
lemma noetherianSpace_of_isProper {T : Scheme.{u}} (q : T ⟶ trait k') [IsProper q] :
    TopologicalSpace.NoetherianSpace T := by
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian q
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace q
  have : IsNoetherian T := ⟨⟩
  infer_instance

omit [IsSepClosed k'] [Fact (ringChar k').Prime] in
/-- A proper scheme over the trait is noetherian. -/
lemma isNoetherian_of_isProper {T : Scheme.{u}} (q : T ⟶ trait k') [IsProper q] :
    IsNoetherian T := by
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian q
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace q
  exact ⟨⟩

variable {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]

/-- **Gabber's Künneth formula for proper models in chart dimension `n`** over the trait
`Spec k'⟦t⟧`: the statement of `NearbyCyclesModel.KunnethFormula` for products of models whose
structure morphisms are proper. -/
def ProperKunnethFormula (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    [IsCommMonObj Λ] (k' : Type u) [Field k'] (n : ℕ) : Prop :=
  ∀ {X Y Z : Scheme.{u}} {X' Y' Z' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
    {N : NearbyCyclesModel Y Y'.left} {P : NearbyCyclesModel Z Z'.left} {f₁ : Z ⟶ X}
    {f₁' : Z'.left ⟶ X'.left} {f₂ : Z ⟶ Y} {f₂' : Z'.left ⟶ Y'.left} (φ₁ : P.Hom M f₁ f₁')
    (φ₂ : P.Hom N f₂ f₂') {qM : M.total ⟶ trait k'}
    {gM : M.generic ⟶ Spec (.of (traitGenericField k'))} {qN : N.total ⟶ trait k'}
    {gN : N.generic ⟶ Spec (.of (traitGenericField k'))},
    M.IsTraitModelOver qM gM → N.IsTraitModelOver qN gN →
    IsPullback φ₁.total φ₂.total qM qN →
    P.IsTraitModelOver (φ₁.total ≫ qM) (φ₁.generic ≫ gM) →
    φ₂.generic ≫ gN = φ₁.generic ≫ gM → IsProper qM → IsProper qN → IsNoetherian X →
    IsNoetherian Y → TopologicalSpace.NoetherianSpace Z → ∀ {m₁ m₂ : ℕ},
    m₁ + m₂ ≤ n → qM.LocallyEmbedsInAffineSpace m₁ → qN.LocallyEmbedsInAffineSpace m₂ →
    ∀ {eM : M.total ⟶ X}, M.j ≫ eM = M.ε → ∀ {eN : N.total ⟶ Y}, N.j ≫ eN = N.ε →
    ∀ {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X))}
      {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj Λ Y))},
      boundedConstructible (condensedRingObj Λ X) A →
      boundedConstructible (condensedRingObj Λ Y) B →
      IsIso (kunnethMap Λ φ₁ φ₂ A B)

omit [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] in
/-- The Künneth formula for products over the trait of proper models with compatible projections
applies to the product `X̄ ×_S Ȳ` of the standard models of proper schemes over the trait. -/
theorem isIso_kunnethMap_closure_of_properKunnethFormula {n : ℕ}
    (hproper : ProperKunnethFormula Λ k' n)
    {Xc Yc : Scheme.{u}} (qcM : Xc ⟶ trait k') (qcN : Yc ⟶ trait k') [IsProper qcM]
    [IsProper qcN] {m₁ m₂ : ℕ} (hle : m₁ + m₂ ≤ n) (h₁ : qcM.LocallyEmbedsInAffineSpace m₁)
    (h₂ : qcN.LocallyEmbedsInAffineSpace m₂)
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Xc) Ab.{u + 1})
      (condensedRingObj Λ Xc)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Yc) Ab.{u + 1})
      (condensedRingObj Λ Yc)))
    (hA : boundedConstructible (condensedRingObj Λ Xc) A)
    (hB : boundedConstructible (condensedRingObj Λ Yc) B) :
    IsIso (kunnethMap Λ (closureFst qcM qcN) (closureSnd qcM qcN) A B)
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
    (by simp) inferInstance inferInstance (isNoetherian_of_isProper qcM)
    (isNoetherian_of_isProper qcN)
    (by
      let q := pullback.snd (C := Scheme.{u}) (pullback.fst qcM qcN ≫ qcM) (traitGenericPoint k')
      have : IsLocallyNoetherian (pullback (C := Scheme.{u}) (pullback.fst qcM qcN ≫ qcM)
        (traitGenericPoint k')) := LocallyOfFiniteType.isLocallyNoetherian q
      have : CompactSpace (pullback (C := Scheme.{u}) (pullback.fst qcM qcN ≫ qcM)
        (traitGenericPoint k')) := QuasiCompact.compactSpace_of_compactSpace q
      have : IsNoetherian (pullback (C := Scheme.{u}) (pullback.fst qcM qcN ≫ qcM)
        (traitGenericPoint k')) := ⟨⟩
      exact (inferInstance : TopologicalSpace.NoetherianSpace (pullback (C := Scheme.{u})
        (pullback.fst qcM qcN ≫ qcM) (traitGenericPoint k')))) hle h₁ h₂ (eM := 𝟙 _)
    (by simp [geometric])
    (eN := 𝟙 _) (by simp [geometric]) hA hB
  have e : (closureFst qcM qcN).generic ≫ pullback.snd qcM (traitGenericPoint k') =
      pullback.snd (pullback.fst qcM qcN ≫ qcM) (traitGenericPoint k') := by simp
  rw [e]
  exact IsPullback.of_hasPullback _ _

omit [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] in
/-- **Reduction of Gabber's Künneth formula to proper models, for a global chart** (blueprint
`proposition-external-kunneth-formula-nearby-cycles`, "Reduction to projective flat families";
Illusie,
*Autour du théorème de monodromie locale*, proof of Thm. 4.7): if the Künneth formula holds for
proper models in chart dimension `n`, then it holds for products over the trait of models whose
total spaces admit immersions into `𝔸(ι_M; S)`, `𝔸(ι_N; S)` with `|ι_M| + |ι_N| ≤ n`.

The Künneth map is that of the models of the total spaces
(`NearbyCyclesModel.isIso_kunnethMap_of_toGeometricGeneric`); these are restrictions of the
standard models of the closures of the total spaces in the projective spaces
(`AlgebraicGeometry.Compactification.ofIsImmersionAffineSpace`), whose charts have the same
dimension
(`AlgebraicGeometry.Compactification.locallyEmbedsInAffineSpace_ofIsImmersionAffineSpace`),
and the coefficients are extended by zero
(`NearbyCyclesModel.isIso_kunnethMap_toGeometricGeneric_of_closure`). -/
theorem isIso_kunnethMap_of_properKunnethFormula_of_isImmersion {n : ℕ}
    (hproper : ProperKunnethFormula Λ k' n) (hM : M.IsTraitModelOver qM gM)
    (hN : N.IsTraitModelOver qN gN) (hpb : IsPullback φ₁.total φ₂.total qM qN)
    (hP : P.IsTraitModelOver (φ₁.total ≫ qM) (φ₁.generic ≫ gM))
    (hgen : φ₂.generic ≫ gN = φ₁.generic ≫ gM)
    {eM : M.total ⟶ X} (heM : M.j ≫ eM = M.ε) {eN : N.total ⟶ Y} (heN : N.j ≫ eN = N.ε)
    {ιM ιN : Type u} [Finite ιM] [Finite ιN] (cM : M.total ⟶ 𝔸(ιM; trait k')) [IsImmersion cM]
    (hcM : cM ≫ 𝔸(ιM; trait k') ↘ trait k' = qM) (cN : N.total ⟶ 𝔸(ιN; trait k'))
    [IsImmersion cN] (hcN : cN ≫ 𝔸(ιN; trait k') ↘ trait k' = qN)
    (hle : Nat.card ιM + Nat.card ιN ≤ n)
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))}
    (hA : boundedConstructible (condensedRingObj Λ X) A)
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))}
    (hB : boundedConstructible (condensedRingObj Λ Y) B) :
    IsIso (kunnethMap Λ φ₁ φ₂ A B) := by
  have := hM.quasiCompact
  have := hN.quasiCompact
  let cpM := Compactification.ofIsImmersionAffineSpace cM hcM
  let cpN := Compactification.ofIsImmersionAffineSpace cN hcN
  have := cpM.isProper
  have := cpN.isProper
  have := cpM.isOpenImmersion
  have := cpN.isOpenImmersion
  have := noetherianSpace_of_isProper cpM.g
  have := noetherianSpace_of_isProper cpN.g
  refine isIso_kunnethMap_of_toGeometricGeneric Λ _ _ heM heN A B ?_
  exact isIso_kunnethMap_toGeometricGeneric_of_closure Λ hM hN hpb hP
    hgen cpM.i cpN.i cpM.comm.symm cpN.comm.symm
    (fun A' B' hA' hB' ↦ isIso_kunnethMap_closure_of_properKunnethFormula hproper cpM.g cpN.g hle
      (Compactification.locallyEmbedsInAffineSpace_ofIsImmersionAffineSpace cM hcM)
      (Compactification.locallyEmbedsInAffineSpace_ofIsImmersionAffineSpace cN hcN) A' B' hA' hB')
    (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ _ _ hA)
    (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ _ _ hB)

omit [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] in
/-- **Reduction of Gabber's Künneth formula to proper models** (blueprint
`proposition-external-kunneth-formula-nearby-cycles`, "Reduction to projective flat families";
Illusie,
*Autour du théorème de monodromie locale*, proof of Thm. 4.7): if the Künneth formula holds for
proper models in chart dimension `n`, then it holds in chart dimension `n`.

The assertion is local on the special fibre
(`NearbyCyclesModel.isIso_kunnethMap_of_forall_exists_restriction`): around each point of the
special fibre the product restricts to the product `V ×_S W` of charts `V`, `W` of the total
spaces, where `NearbyCyclesModel.isIso_kunnethMap_of_properKunnethFormula_of_isImmersion`
applies. -/
theorem isIso_kunnethMap_of_properKunnethFormula {n : ℕ}
    (hproper : ProperKunnethFormula Λ k' n) (hM : M.IsTraitModelOver qM gM)
    (hN : N.IsTraitModelOver qN gN) (hpb : IsPullback φ₁.total φ₂.total qM qN)
    (hP : P.IsTraitModelOver (φ₁.total ≫ qM) (φ₁.generic ≫ gM))
    (hgen : φ₂.generic ≫ gN = φ₁.generic ≫ gM) {m m' : ℕ} (hle : m + m' ≤ n)
    (hm : qM.LocallyEmbedsInAffineSpace m) (hm' : qN.LocallyEmbedsInAffineSpace m')
    {eM : M.total ⟶ X} (heM : M.j ≫ eM = M.ε) {eN : N.total ⟶ Y} (heN : N.j ≫ eN = N.ε)
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))}
    (hA : boundedConstructible (condensedRingObj Λ X) A)
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))}
    (hB : boundedConstructible (condensedRingObj Λ Y) B) :
    IsIso (kunnethMap Λ φ₁ φ₂ A B) := by
  have := hM.isTraitModel.isNoetherian_total
  have := hN.isTraitModel.isNoetherian_total
  have := hP.isTraitModel.isNoetherian_total
  have : LocallyOfFiniteType Z'.hom :=
    MorphismProperty.of_isPullback hP.isPullback_i hP.locallyOfFiniteType
  have : QuasiCompact Z'.hom := MorphismProperty.of_isPullback hP.isPullback_i hP.quasiCompact
  have : IsLocallyNoetherian Z'.left := LocallyOfFiniteType.isLocallyNoetherian Z'.hom
  have : CompactSpace Z'.left := QuasiCompact.compactSpace_of_compactSpace Z'.hom
  have : IsNoetherian Z'.left := ⟨⟩
  refine isIso_kunnethMap_of_forall_exists_restriction Λ φ₁ φ₂ A B fun
      z ↦ ?_
  obtain ⟨V, hzV, ιV, _, cV, hcardV, hcVi, hcV⟩ := hm (φ₁.total (P.i z))
  obtain ⟨W, hzW, ιW, _, cW, hcardW, hcWi, hcW⟩ := hm' (φ₂.total (P.i z))
  have : QuasiCompact V.ι := inferInstance
  have : QuasiCompact W.ι := inferInstance
  have : QuasiCompact (productOpen φ₁ φ₂ V W).ι := inferInstance
  refine ⟨P.i ⁻¹ᵁ productOpen φ₁ φ₂ V W, _, _, _, _, _, M.restrictOpen V, N.restrictOpen W,
    P.restrictOpen (productOpen φ₁ φ₂ V W), f₁, _, f₂, _, 𝟙 X, _, 𝟙 Y, _, 𝟙 Z,
    φ₁.restrictOpen _ V inf_le_left, φ₂.restrictOpen _ W inf_le_right, M.restrictOpenHom V,
    N.restrictOpenHom W, P.restrictOpenHom _, ⟨hzV, hzW⟩,
    isKunnethRestriction_restrictOpen φ₁ φ₂ V W, ?_⟩
  exact isIso_kunnethMap_of_properKunnethFormula_of_isImmersion hproper (hM.restrictOpen V)
    (hN.restrictOpen W) (isPullback_resLE_inf hpb V W)
    (isTraitModelOver_restrictOpen_productOpen (φ₂ := φ₂) hP V W)
    (by simp [Scheme.Hom.resLE_comp_ι_assoc, hgen]) (eM := V.ι ≫ eM) (by simp [← heM])
    (eN := W.ι ≫ eN) (by simp [← heN]) cV hcV cW hcW (by omega)
    ((boundedConstructible _).prop_of_iso ((leftDerivedUpperStarId Λ
        X).app A).symm hA)
    ((boundedConstructible _).prop_of_iso ((leftDerivedUpperStarId Λ
        Y).app B).symm hB)

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
