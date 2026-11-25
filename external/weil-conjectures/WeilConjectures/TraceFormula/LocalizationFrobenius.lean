/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek
public import WeilConjectures.TraceFormula.CompactCohomology
public import WeilConjectures.TraceFormula.OpenPieceCoherence
public import WeilConjectures.CategoryTheory.Triangulated.TriangleMorphismExtension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarShift
public import WeilConjectures.TraceFormula.CompactPullbackShift

/-!

# The Frobenius endomorphisms of the open–closed localization triangle

Let `Φ` be a finite universal homeomorphism of `X`, `j : U ⟶ X` an open immersion and
`i : Z ⟶ X` a closed immersion onto the complement, both stable under `Φ`. For a Weil object
`(K, φ)` this file defines the endomorphisms `E_U` and `E_Z` of `RΓ_c(X, Rj_! Lj^* K)` and
`RΓ_c(X, Ri_* Li^* K)` induced by the compactly supported Frobenii of `K|_U` and `K|_Z`, and shows
that they are compatible with the counit `Rj_! Lj^* K ⟶ K` and the unit `K ⟶ Ri_* Li^* K` of the
localization triangle (blueprint `lemma-additivity-open-subscheme-complement`,
`lemma-additivity-open-subscheme-complement`).

## Main definitions

- `ProEtale.CondensedRing.WeilBoundedConstructible.compactFrobeniusOpenPiece`: the operator `E_U`.
- `ProEtale.CondensedRing.WeilBoundedConstructible.compactFrobeniusClosedPiece`: the operator
  `E_Z`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section Adjunction

variable {X U Z : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  (j : U ⟶ X) [IsOpenImmersion j.left] (i : Z ⟶ X) [IsClosedImmersion i.left]

variable (ℓ) in
/-- The adjunction `Rj_! ⊣ Lj^*` of an open immersion: the adjunction `Rj_! ⊣ Rj^!` transported
along `Rj^! ≅ Lj^*`. -/
noncomputable def boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl :
    boundedConstructibleLowerShriek ℓ j ⊣
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j :=
  (boundedConstructibleUpperShriekAdjunction ℓ j).ofNatIsoRight
    (boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ j)

end Adjunction

/-! ### The Frobenius endomorphisms of the triangle -/

/-- The abstract shape of the compatibility of the compactly supported Frobenius with the pullback
to a closed piece: the composition laws `(i ≫ Φ)^♯ = Φ^♯ ≫ i^♯` and `(Φ_Z ≫ i)^♯ = i^♯ ≫ Φ_Z^♯`
and `Φ_Z ≫ i = i ≫ Φ`. -/
lemma frobenius_closedPiece_aux {CX CZ D : Type*} [Category CX] [Category CZ] [Category D]
    {aX : CX ⥤ D} {aZ : CZ ⥤ D} {uΦ : CX ⥤ CX} {ui : CX ⥤ CZ} {uΦZ : CZ ⥤ CZ} {u₁ u₂ : CX ⥤ CZ}
    (pΦ : aX ⟶ uΦ ⋙ aX) (pi : aX ⟶ ui ⋙ aZ) (pΦZ : aZ ⟶ uΦZ ⋙ aZ) (p₁ : aX ⟶ u₁ ⋙ aZ)
    (p₂ : aX ⟶ u₂ ⋙ aZ) (c₁ : u₁ ≅ uΦ ⋙ ui) (c₂ : u₂ ≅ ui ⋙ uΦZ) (K : CX)
    (e : u₂.obj K ⟶ u₁.obj K)
    (h1 : p₁.app K = pΦ.app K ≫ pi.app (uΦ.obj K) ≫ aZ.map (c₁.inv.app K))
    (h2 : p₂.app K = pi.app K ≫ pΦZ.app (ui.obj K) ≫ aZ.map (c₂.inv.app K))
    (h3 : p₂.app K ≫ aZ.map e = p₁.app K) (cmp : uΦZ.obj (ui.obj K) ⟶ ui.obj (uΦ.obj K))
    (hc : cmp = c₂.inv.app K ≫ e ≫ c₁.hom.app K) (φ : uΦ.obj K ⟶ K) (cF : aX.obj K ⟶ aX.obj K)
    (hK : cF = pΦ.app K ≫ aX.map φ) (ψ : uΦZ.obj (ui.obj K) ⟶ ui.obj K)
    (cFZ : aZ.obj (ui.obj K) ⟶ aZ.obj (ui.obj K)) (hKZ : cFZ = pΦZ.app (ui.obj K) ≫ aZ.map ψ)
    (hψ : ψ = cmp ≫ ui.map φ) :
    cF ≫ pi.app K = pi.app K ≫ cFZ := by
  have hn := pi.naturality φ
  simp only [Functor.comp_map] at hn
  rw [hK, hKZ, hψ, hc, Category.assoc, hn]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% h2, reassoc_of% h3, h1]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc aZ (c₁.inv.app K) (c₁.hom.app K), Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- The inverse of `a⁻¹ ≫ (G = H) ≫ b` at an object. -/
lemma iso_symm_trans_eqToIso_trans_inv_app {C D : Type*} [Category C] [Category D]
    {F G H I : C ⥤ D} (a : F ≅ G) (h : F = H) (b : H ≅ I) (K : C) :
    (a.symm ≪≫ eqToIso h ≪≫ b).inv.app K =
      b.inv.app K ≫ eqToHom (congrArg (fun T ↦ T.obj K) h.symm) ≫ a.hom.app K := by
  subst h
  simp

/-- `comp_eq_comp_conj_of_comp_eq` for the component of a natural isomorphism. -/
lemma comp_eq_comp_conj_of_comp_eq_app {B C D : Type*} [Category B] [Category C] [Category D]
    {F₁ : B ⥤ C} {F₂ : C ⥤ D} {G : B ⥤ D} (γ : F₁ ⋙ F₂ ≅ G) (M : B) {a : D} (x : a ⟶ a)
    (y : a ⟶ F₂.obj (F₁.obj M)) (z : G.obj M ⟶ G.obj M)
    (h : x ≫ y ≫ γ.hom.app M = (y ≫ γ.hom.app M) ≫ z) :
    x ≫ y = y ≫ γ.hom.app M ≫ z ≫ γ.inv.app M := by
  rw [← cancel_mono (γ.hom.app M)]
  simpa using h

/-- An endomorphism commuting with `y ≫ g` for an isomorphism `g` commutes with `y` and the
conjugate along `g`. -/
lemma comp_eq_comp_conj_of_comp_eq {D : Type*} [Category D] {a b c : D} (x : a ⟶ a) (y : a ⟶ b)
    (g : b ≅ c) (z : c ⟶ c) (h : x ≫ y ≫ g.hom = (y ≫ g.hom) ≫ z) :
    x ≫ y = y ≫ g.hom ≫ z ≫ g.inv := by
  rw [← cancel_mono g.hom]
  simpa using h

section Frobenius

variable {X U Z : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]

variable (ℓ) in
/-- The isomorphism `Ra_{X!} Ri_* ≅ Ra_{X!} Ri_! ≅ Ra_{Z!}` for a proper `i : Z ⟶ X`. -/
noncomputable def boundedConstructibleLowerStarCompToPoint (i : Z ⟶ X) [IsProper i.left] :
    boundedConstructibleLowerStar ℓ i ⋙
        boundedConstructibleLowerShriek ℓ (toPoint X) ≅
      boundedConstructibleLowerShriek ℓ (toPoint Z) :=
  Functor.isoWhiskerRight (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ i).symm _ ≪≫
    boundedConstructibleLowerShriekCompToPoint ℓ i

/-- The pullback `i^♯ : Ra_{X!} ⟶ Ra_{Z!} Li^*` along a proper `i` is `Ra_{X!}` of the unit of
`Li^* ⊣ Ri_*` followed by `Ra_{X!} Ri_* ≅ Ra_{Z!}`. -/
lemma compactPullback_app_eq (i : Z ⟶ X) [IsProper i.left]
    (N : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (compactPullback ℓ i).app N =
      (boundedConstructibleLowerShriek ℓ (toPoint X)).map
          ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
            i).unit.app N) ≫
        (boundedConstructibleLowerStarCompToPoint ℓ i).hom.app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj N) := by
  rw [compactPullback_app, boundedConstructibleLowerStarCompToPoint, Iso.trans_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Iso.symm_hom]

variable {Φ : X ⟶ X} {ΦU : U ⟶ U} {ΦZ : Z ⟶ Z} {j : U ⟶ X} {i : Z ⟶ X}
  [IsOpenImmersion j.left] [IsClosedImmersion i.left] [IsFinite Φ.left]
  [IsUniversalHomeomorphism Φ.left] [IsFinite ΦU.left] [IsUniversalHomeomorphism ΦU.left]
  [IsFinite ΦZ.left] [IsUniversalHomeomorphism ΦZ.left]

namespace WeilBoundedConstructible

omit [IsClosedImmersion i.left] [IsFinite Φ.left] [IsUniversalHomeomorphism Φ.left]
  [IsFinite ΦZ.left] [IsUniversalHomeomorphism ΦZ.left] in
/-- The Frobenius structure of the restriction `K|_Z`. -/
lemma weilUpperStar_obj_str_hom (hi : ΦZ ≫ i = i ≫ Φ) (K : WeilBoundedConstructible ℓ Φ) :
    ((weilUpperStar ℓ ΦZ Φ i hi).obj K).str.hom =
      (weilUpperStarComparison ℓ ΦZ Φ i hi).hom.app K.carrier ≫
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).map K.str.hom := by
  rw [weilUpperStar_obj_str ℓ ΦZ Φ i hi K]
  rfl

omit [IsClosedImmersion i.left] [IsFinite Φ.left] [IsUniversalHomeomorphism Φ.left] in
/-- The compactly supported Frobenius of the restriction `K|_Z` as `RΓ_c(φ|_Z) ∘ Φ_Z^♯`. -/
lemma compactFrobenius_weilUpperStar (hi : ΦZ ≫ i = i ≫ Φ) (K : WeilBoundedConstructible ℓ Φ) :
    ((weilUpperStar ℓ ΦZ Φ i hi).obj K).compactFrobenius =
      (compactPullback ℓ ΦZ).app ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        i).obj K.carrier) ≫
        (boundedConstructibleLowerShriek ℓ (toPoint Z)).map
          ((weilUpperStarComparison ℓ ΦZ Φ i hi).hom.app K.carrier ≫
            (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).map K.str.hom) := by
  rw [compactFrobenius_eq (X := Z) (Φ := ΦZ) ((weilUpperStar ℓ ΦZ Φ i hi).obj K),
    weilUpperStar_obj_str_hom]
  -- the carrier of `K|_Z` is `Li^* K` by `rfl`; a bare `rfl` slowly unfolded the composites
  dsimp only [weilUpperStar_obj_carrier]

-- the coherence of the pullbacks along `Φ_Z ≫ i = i ≫ Φ` is a long elaboration
omit [IsUniversalHomeomorphism ΦZ.left] in
/-- **The compactly supported Frobenius commutes with the pullback to a closed piece**: for a
closed immersion `i` with `Φ_Z ≫ i = i ≫ Φ`, `i^♯ ∘ F_c(K) = F_c(K|_Z) ∘ i^♯`. Through
`F_c = RΓ_c(φ) ∘ Φ^♯` this is the composition law of the pullbacks along
`Φ_Z ≫ i = i ≫ Φ`. -/
theorem compactFrobenius_comp_compactPullback (hi : ΦZ ≫ i = i ≫ Φ)
    (K : WeilBoundedConstructible ℓ Φ) :
    K.compactFrobenius ≫ (compactPullback ℓ i).app K.carrier =
      (compactPullback ℓ i).app K.carrier ≫
        ((compactPullback ℓ ΦZ).app ((boundedConstructibleUpperStar
          (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K.carrier) ≫
          (boundedConstructibleLowerShriek ℓ (toPoint Z)).map
            ((weilUpperStarComparison ℓ ΦZ Φ i hi).hom.app K.carrier ≫
              (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).map
                K.str.hom)) := by
  have : IsProper (i ≫ Φ).left := by
    rw [Over.comp_left]
    infer_instance
  have : IsProper (ΦZ ≫ i).left := by
    rw [Over.comp_left]
    infer_instance
  exact frobenius_closedPiece_aux (compactPullback ℓ Φ) (compactPullback ℓ i)
    (compactPullback ℓ ΦZ) (compactPullback ℓ (i ≫ Φ)) (compactPullback ℓ (ΦZ ≫ i))
    (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ i Φ)
    (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ ΦZ i) K.carrier
    (eqToHom (by rw [hi])) (compactPullback_comp_app ℓ i Φ K.carrier)
    (compactPullback_comp_app ℓ ΦZ i K.carrier) (compactPullback_app_congr ℓ hi K.carrier)
    ((weilUpperStarComparison ℓ ΦZ Φ i hi).hom.app K.carrier)
    (weilUpperStarComparison_hom_app ℓ ΦZ Φ i hi K.carrier) K.str.hom _
    (compactFrobenius_eq K) _ _ rfl rfl

variable (ℓ) in
/-- The operator `E_U` on `RΓ_c(X, Rj_! Lj^* K)`: the compactly supported Frobenius of the
restriction `K|_U`, transported along `Ra_{X!} Rj_! ≅ Ra_{U!}`. -/
noncomputable def compactFrobeniusOpenPiece (hj : ΦU ≫ j = j ≫ Φ)
    (K : WeilBoundedConstructible ℓ Φ) :
    (boundedConstructibleLowerShriek ℓ (toPoint X)).obj
        ((boundedConstructibleLowerShriek ℓ j).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K.carrier)) ⟶
      (boundedConstructibleLowerShriek ℓ (toPoint X)).obj
        ((boundedConstructibleLowerShriek ℓ j).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K.carrier)) :=
  (boundedConstructibleLowerShriekCompToPoint ℓ j).hom.app
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K.carrier) ≫
    ((weilUpperStar ℓ ΦU Φ j hj).obj K).compactFrobenius ≫
    (boundedConstructibleLowerShriekCompToPoint ℓ j).inv.app
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K.carrier)

variable (ℓ) in
/-- The operator `E_Z` on `RΓ_c(X, Ri_* Li^* K)`: the compactly supported Frobenius of the
restriction `K|_Z`, transported along `Ra_{X!} Ri_* ≅ Ra_{Z!}`. -/
noncomputable def compactFrobeniusClosedPiece (hi : ΦZ ≫ i = i ≫ Φ)
    (K : WeilBoundedConstructible ℓ Φ) :
    (boundedConstructibleLowerShriek ℓ (toPoint X)).obj
        ((boundedConstructibleLowerStar ℓ i).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K.carrier)) ⟶
      (boundedConstructibleLowerShriek ℓ (toPoint X)).obj
        ((boundedConstructibleLowerStar ℓ i).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K.carrier)) :=
  (boundedConstructibleLowerStarCompToPoint ℓ i).hom.app
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K.carrier) ≫
    ((compactPullback ℓ ΦZ).app ((boundedConstructibleUpperStar
      (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K.carrier) ≫
      (boundedConstructibleLowerShriek ℓ (toPoint Z)).map
        ((weilUpperStarComparison ℓ ΦZ Φ i hi).hom.app K.carrier ≫
          (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).map K.str.hom)) ≫
    (boundedConstructibleLowerStarCompToPoint ℓ i).inv.app
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K.carrier)

-- the closed-piece operator unfolds to a long composite
omit [IsUniversalHomeomorphism ΦZ.left] in
/-- The square of the closed piece: `E_Z ∘ RΓ_c(η) = RΓ_c(η) ∘ F_c(K)` for the unit
`η : K ⟶ Ri_* Li^* K`. -/
theorem compactFrobenius_comp_compactUnit (hi : ΦZ ≫ i = i ≫ Φ)
    (K : WeilBoundedConstructible ℓ Φ) :
    K.compactFrobenius ≫
        (boundedConstructibleLowerShriek ℓ (toPoint X)).map
          ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
            i).unit.app K.carrier) =
      (boundedConstructibleLowerShriek ℓ (toPoint X)).map
          ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
            i).unit.app K.carrier) ≫ compactFrobeniusClosedPiece ℓ hi K := by
  have e := compactPullback_app_eq (ℓ := ℓ) i K.carrier
  have h : K.compactFrobenius ≫
      (boundedConstructibleLowerShriek ℓ (toPoint X)).map
        ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
          i).unit.app K.carrier) ≫
        (boundedConstructibleLowerStarCompToPoint ℓ i).hom.app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K.carrier) =
      ((boundedConstructibleLowerShriek ℓ (toPoint X)).map
        ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
          i).unit.app K.carrier) ≫
        (boundedConstructibleLowerStarCompToPoint ℓ i).hom.app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K.carrier)) ≫
        ((compactPullback ℓ ΦZ).app ((boundedConstructibleUpperStar
          (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K.carrier) ≫
          (boundedConstructibleLowerShriek ℓ (toPoint Z)).map
            ((weilUpperStarComparison ℓ ΦZ Φ i hi).hom.app K.carrier ≫
              (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).map
                K.str.hom)) := by
    rw [← e]
    exact compactFrobenius_comp_compactPullback hi K
  rw [compactFrobeniusClosedPiece,
    ← cancel_mono ((boundedConstructibleLowerStarCompToPoint ℓ i).hom.app
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K.carrier)),
    Category.assoc, h]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

-- the open-piece operator unfolds to a long composite
omit [IsClosedImmersion i.left] in
/-- The square of the open piece (blueprint `lemma-additivity-open-subscheme-complement`, Step
2(a)): `RΓ_c(ε) ∘ E_U = F_c(K) ∘ RΓ_c(ε)` for the counit `ε : Rj_! Lj^* K ⟶ K`. Through
`F_c = RΓ_c(φ) ∘ Φ^♯` this is the compatibility of the extension by zero with the pullbacks along
the Frobenii, `compToPoint_inv_app_comp_counit_comp_compactPullback`. -/
theorem compactFrobeniusOpenPiece_comp_counit (hj : ΦU ≫ j = j ≫ Φ)
    (K : WeilBoundedConstructible ℓ Φ) :
    compactFrobeniusOpenPiece ℓ hj K ≫
        (boundedConstructibleLowerShriek ℓ (toPoint X)).map
          ((boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl ℓ j).counit.app
            K.carrier) =
      (boundedConstructibleLowerShriek ℓ (toPoint X)).map
          ((boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl ℓ j).counit.app
            K.carrier) ≫ K.compactFrobenius := by
  have h := compToPoint_inv_app_comp_counit_comp_compactPullback ℓ j hj K.carrier
  have hn₁ := (boundedConstructibleLowerShriekCompToPoint ℓ j).inv.naturality
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).map K.str.hom)
  have hn₂ := congrArg
    (boundedConstructibleLowerShriek ℓ (toPoint X)).map
    ((boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl ℓ j).counit.naturality
      K.str.hom)
  simp only [Functor.comp_map, Functor.comp_obj] at hn₁
  simp only [Functor.comp_map, Functor.id_map, Functor.map_comp, Functor.comp_obj,
    Functor.id_obj] at hn₂
  rw [boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl] at hn₂ ⊢
  rw [compactFrobeniusOpenPiece,
    ← cancel_epi ((boundedConstructibleLowerShriekCompToPoint ℓ j).inv.app
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K.carrier))]
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_app_assoc, compactFrobenius_eq K, reassoc_of% h]
  -- `rw`, not `Eq.trans (congrArg _ _)`: elaborating the latter against the goal was slow
  rw [compactFrobenius_weilUpperStar hj K]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn₁, hn₂]

end WeilBoundedConstructible

end Frobenius

end AlgebraicGeometry.ProEtale.CondensedRing
