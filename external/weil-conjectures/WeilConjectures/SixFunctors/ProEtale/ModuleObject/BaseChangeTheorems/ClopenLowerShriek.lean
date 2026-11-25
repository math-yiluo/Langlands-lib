/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriekIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.PullbackSquareComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionIdIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.RefinementCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit

/-!

# The lower shriek of an open and closed immersion

For an open immersion `j : U ⟶ X` which is also proper, the derived lower shriek `Rj_!` on
bounded constructible `ℚ̄_ℓ`-sheaves has two identifications: with the extension by zero `j_!`
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl`,
through the compactification `U ⟶[j] X ⟶[𝟙] X`) and with the derived pushforward `Rj_*`
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl`, through the
compactification `U ⟶[𝟙] U ⟶[j] X`). This file expresses the composite `j_! ≅ Rj_! ≅ Rj_*`
through the single refinement `j` of the first compactification by the second
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_inv_comp`).

## Compactification coherence

The clauses of blueprint `proposition-construction-independence-rf-shriek` (subsection
`sk-prop-sf-cbc` of the six-functor chapter) used here, for the lower shriek of bounded
constructible complexes attached to compactifications (proved in
`…LowerShriek.RefinementCoherence` through the equalizer of two refinements):

- the comparison of two compactifications through a common refinement does not depend on the
  refinement, so it is the comparison along any given refinement
  (`ProEtale.CondensedRing.boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_eq`);
- the comparisons satisfy the cocycle condition
  (`ProEtale.CondensedRing.boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_trans`);
- the comparisons along refinements are transitive under composition
  (`ProEtale.CondensedRing.boundedConstructibleLowerShriekRefinementIso'_trans`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### Compactification coherence -/

section Coherence

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Z Z₁ Z₂ Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Z₁.hom] [QuasiCompact Z₁.hom]
  [IsSeparated Z₁.hom] [LocallyOfFiniteType Z₂.hom] [QuasiCompact Z₂.hom] [IsSeparated Z₂.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- Blueprint `proposition-construction-independence-rf-shriek`, transitivity clause ("these
transformations are identities for identity refinements and are transitive under
composition"): for refinements `h : Z ⟶ Z₁` and `h₁ : Z₁ ⟶ Z₂` of factorizations
`X ⟶[i] Z ⟶[p] Y`, `X ⟶[i₁] Z₁ ⟶[p₁] Y` and `X ⟶[i₂] Z₂ ⟶[p₂] Y`, the comparison along the
composite `h ≫ h₁` is the composite of the comparisons. The blueprint states the clause for
refinements of compactifications; it is used here for factorizations with an open immersion
followed by an arbitrary morphism, such as `U ⟶[j] X ⟶[𝟙] X`, which are compactifications up to
the identification of the middle object. -/
theorem boundedConstructibleLowerShriekRefinementIso'_trans {i : X ⟶ Z} {i₁ : X ⟶ Z₁}
    {i₂ : X ⟶ Z₂} [IsOpenImmersion i.left] [IsOpenImmersion i₁.left] [IsOpenImmersion i₂.left]
    {h : Z ⟶ Z₁} {h₁ : Z₁ ⟶ Z₂} {h₂ : Z ⟶ Z₂} (sq : IsPullback (𝟙 X) i i₁ h)
    (sq₁ : IsPullback (𝟙 X) i₁ i₂ h₁) (sq₂ : IsPullback (𝟙 X) i i₂ h₂) (_hh : h ≫ h₁ = h₂)
    {p : Z ⟶ Y} {p₁ : Z₁ ⟶ Y} {p₂ : Z₂ ⟶ Y} (wp : h ≫ p₁ = p) (wp₁ : h₁ ≫ p₂ = p₁)
    (wp₂ : h₂ ≫ p₂ = p)
    [IsIso (boundedConstructibleLowerStarOpenImmersionLowerShriekExchange' ℓ sq)]
    [IsIso (boundedConstructibleLowerStarOpenImmersionLowerShriekExchange' ℓ sq₁)]
    [IsIso (boundedConstructibleLowerStarOpenImmersionLowerShriekExchange' ℓ sq₂)] :
    boundedConstructibleLowerShriekRefinementIso' ℓ sq₁ wp₁ ≪≫
        boundedConstructibleLowerShriekRefinementIso' ℓ sq wp =
      boundedConstructibleLowerShriekRefinementIso' ℓ sq₂ wp₂ :=
  boundedConstructibleLowerShriekRefinementIso'_trans_eq ℓ sq sq₁ sq₂ _hh wp wp₁ wp₂

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] {f : X ⟶ Y}

/-- Blueprint `proposition-construction-independence-rf-shriek`, cocycle clause ("the resulting
comparison is independent of that choice and satisfies the cocycle condition for triples of
compactifications"), for bounded constructible `ℚ̄_ℓ`-sheaves. -/
theorem boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_trans
    (c₁ c₂ c₃ : Compactification f.left) :
    boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ c₁ c₂ ≪≫
        boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ c₂ c₃ =
      boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ c₁ c₃ :=
  boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_trans_eq ℓ c₁ c₂ c₃

/-- Blueprint `proposition-construction-independence-rf-shriek`, refinement clause ("for a
refinement `u : c₁ → c₂`, the canonical transformation between the compact-support candidates is the
composite of the proper-composition isomorphism with the isomorphism `Ru_* j_{1!} ≅ j_{2!}`";
"comparison through a common refinement gives a natural isomorphism", independent of the choice
of the refinement): the comparison of `c₁` with a refinement `c` of `c₁` is the comparison along
the refinement. -/
theorem boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_eq
    {c c₁ : Compactification f.left} (r : Compactification.OverRefinement c c₁) :
    haveI := r.isProper
    haveI := isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'_padicAlgCl ℓ
      r.isPullback
    boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ c₁ c =
      boundedConstructibleLowerShriekRefinementIso' ℓ r.isPullback r.hom_overG :=
  boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_eq_refinementIso ℓ r

end Coherence

/-! ### The abstract computation -/

section Abstract

/-- The computation behind `boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_clopen`, for
abstract functors: `jS ⊣ Lj` stands for `j_! ⊣ Lj^*`, `Lj ⊣ Rj` for `Lj^* ⊣ Rj_*`, `L1 ⊣ R1`
for `L(𝟙 U)^* ⊣ R(𝟙 U)_*`, `iS` for the extension by zero `(𝟙 U)_!`, `RX1` for `R(𝟙 X)_*`,
`BC` for the base change `j_! ⋙ Lj^* ≅ L(𝟙 U)^* ⋙ (𝟙 U)_!` and `Exch` for the exchange morphism
`R(𝟙 U)_* ⋙ j_! ⟶ (𝟙 U)_! ⋙ Rj_*`. -/
lemma clopen_comparison_aux {DU DX : Type*} [Category DU] [Category DX]
    {jS : DU ⥤ DX} {Lj : DX ⥤ DU} {Rj : DU ⥤ DX} (a : jS ⊣ Lj) (b : Lj ⊣ Rj)
    {L1 R1 iS : DU ⥤ DU} (b1 : L1 ⊣ R1) (ui : L1 ≅ 𝟭 DU) (idU : R1 ≅ 𝟭 DU) (ι : iS ≅ 𝟭 DU)
    (BC : jS ⋙ Lj ≅ L1 ⋙ iS) {RX1 : DX ⥤ DX} (idX : RX1 ≅ 𝟭 DX) (comp : Rj ⋙ RX1 ≅ Rj)
    (Exch : R1 ⋙ jS ⟶ iS ⋙ Rj)
    (hF1 : ∀ N, idX.inv.app (Rj.obj N) ≫ comp.hom.app N = 𝟙 _)
    (hF2 : ∀ M, idU.inv.app M ≫ ui.inv.app (R1.obj M) ≫ b1.counit.app M = 𝟙 _)
    (hF3 : ∀ N, a.unit.app N ≫ BC.hom.app N ≫ ι.hom.app (L1.obj N) = ui.inv.app N)
    (hEx : ∀ M, Exch.app M = b.unit.app (jS.obj (R1.obj M)) ≫
      Rj.map (BC.hom.app (R1.obj M)) ≫ Rj.map (iS.map (b1.counit.app M)))
    (M : DU) :
    a.unit.app M ≫ Lj.map (idX.inv.app (jS.obj M) ≫
        RX1.map (jS.map (idU.inv.app M) ≫ Exch.app M) ≫ comp.hom.app (iS.obj M) ≫
          Rj.map (ι.hom.app M)) ≫ b.counit.app M = 𝟙 M := by
  have h1 : idX.inv.app (jS.obj M) ≫ RX1.map (jS.map (idU.inv.app M) ≫ Exch.app M) ≫
      comp.hom.app (iS.obj M) = jS.map (idU.inv.app M) ≫ Exch.app M := by
    have hn : idX.inv.app (jS.obj M) ≫ RX1.map (jS.map (idU.inv.app M) ≫ Exch.app M) =
        (jS.map (idU.inv.app M) ≫ Exch.app M) ≫ idX.inv.app (Rj.obj (iS.obj M)) :=
      (idX.inv.naturality (jS.map (idU.inv.app M) ≫ Exch.app M)).symm
    rw [reassoc_of% hn, hF1]
    simp
  have h2 : idX.inv.app (jS.obj M) ≫ RX1.map (jS.map (idU.inv.app M) ≫ Exch.app M) ≫
      comp.hom.app (iS.obj M) ≫ Rj.map (ι.hom.app M) =
        (jS.map (idU.inv.app M) ≫ Exch.app M) ≫ Rj.map (ι.hom.app M) := by
    rw [reassoc_of% h1, Category.assoc]
  rw [h2, hEx]
  have hn1 := a.unit.naturality (idU.inv.app M)
  have hn2 : iS.map (b1.counit.app M) ≫ ι.hom.app M =
      ι.hom.app (L1.obj (R1.obj M)) ≫ b1.counit.app M := ι.hom.naturality (b1.counit.app M)
  simp only [Functor.id_map] at hn1
  simp only [Functor.map_comp, Category.assoc, Functor.id_obj, Adjunction.counit_naturality,
    Adjunction.counit_naturality_assoc, Adjunction.left_triangle_components_assoc]
  rw [← reassoc_of% hn1, hn2, reassoc_of% (hF3 (R1.obj M)), hF2]
  rfl

end Abstract

/-! ### Unit laws of the derived pushforward -/

section LowerStarUnit

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The identity isomorphism `R(𝟙 X)_* ≅ 𝟭` is `R(𝟙 X)_* ≅ L(𝟙 X)^* R(𝟙 X)_* ⟶ 𝟭`, the inverse
of `L(𝟙 X)^* ≅ 𝟭` followed by the counit. -/
lemma boundedConstructibleLowerStarId_hom_app (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerStarId ℓ X).hom.app K =
      (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X).inv.app
          ((boundedConstructibleLowerStar ℓ (𝟙 X)).obj K) ≫
        (boundedConstructibleUpperStarLowerStarAdjunction ℓ (𝟙 X)).counit.app K := by
  simp [boundedConstructibleLowerStarId]

/-- **Right unit law** for the composition isomorphisms of the derived pushforwards on bounded
constructible complexes. -/
lemma boundedConstructibleLowerStarId_inv_app_comp_lowerStarComp_hom_app (g : Y ⟶ X)
    (N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerStarId ℓ X).inv.app ((boundedConstructibleLowerStar ℓ g).obj N) ≫
        (boundedConstructibleLowerStarComp ℓ g (𝟙 X)).hom.app N =
      eqToHom (by simp) := by
  have key (n : Y ⟶ X) (e : n = g)
      (v : boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ n ≅
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (𝟙 X) ⋙
            boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g)
      (hv : ∀ K, v.hom.app K ≫ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          g).map
        ((boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X).hom.app K) = eqToHom
            (by simp [e])) :
      (boundedConstructibleLowerStarId ℓ X).inv.app
          ((boundedConstructibleLowerStar ℓ g).obj N) ≫
        ((conjugateIsoEquiv (boundedConstructibleUpperStarLowerStarAdjunction ℓ n)
          ((boundedConstructibleUpperStarLowerStarAdjunction ℓ (𝟙 X)).comp
            (boundedConstructibleUpperStarLowerStarAdjunction ℓ g)) v.symm).symm).hom.app N =
        eqToHom (by simp [e]) := by
    subst e
    have hv' (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) : v.hom.app K =
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ n).map
        ((boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X).inv.app K) := by
      rw [← cancel_mono ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ n).map
        ((boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X).hom.app K)), hv K, ←
            Functor.map_comp,
        Iso.inv_hom_id_app]
      simp
    simp only [Iso.symm_hom, conjugateIsoEquiv_apply_inv, Iso.symm_inv, conjugateEquiv_apply_app,
      Adjunction.comp_counit_app, hv', Functor.comp_obj, Functor.id_obj, Functor.map_comp]
    rw [Adjunction.unit_naturality_assoc, Adjunction.unit_naturality_assoc,
      Adjunction.right_triangle_components, Category.comp_id,
      ← boundedConstructibleLowerStarId_hom_app, Iso.inv_hom_id_app]
    simp
  exact key _ (Category.comp_id g) _
    (fun K ↦ boundedConstructibleUpperStarComp_id_right_app (Profinite.padicAlgClRingObj ℓ) ℓ g K)

end LowerStarUnit

/-! ### The extension by zero along the identity -/

section IdAdjunction

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The derived adjunction `D((𝟙 X)_!) ⊣ L(𝟙 X)^*` is identified with the identity adjunction
by `D((𝟙 X)_!) ≅ 𝟭` and `L(𝟙 X)^* ≅ 𝟭`: `ι⁻¹ ≫ ε = u` on `L(𝟙 X)^*`. -/
lemma derivedOpenImmersionLowerShriekId_inv_app_comp_counit (X : Scheme.{u})
    (W : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    (derivedOpenImmersionLowerShriekId Λ X).inv.app (L((𝟙 X)^*⟦Λ⟧).obj W) ≫
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ (𝟙 X)).ofNatIsoRight
        (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion Λ (𝟙 X)).symm).counit.app
          W =
      (leftDerivedUpperStarId Λ X).hom.app W := by
  have hn := (derivedOpenImmersionLowerShriekId Λ X).inv.naturality
    ((leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion Λ (𝟙 X)).hom.app W)
  simp only [Functor.id_map] at hn
  have hc := Adjunction.mapDerivedCategoryAdjunction_counit_app_of_iso
    (openImmersionLowerShriekUpperStarAdjunction Λ (𝟙 X)) (openImmersionLowerShriekId Λ X)
    (upperStarId Λ X)
    (Adjunction.leftAdjointUniq_ofNatIsoRight_inv_app_comp_counit _ _) W
  simp only [Adjunction.ofNatIsoRight_counit, NatTrans.comp_app, Iso.symm_inv,
    Functor.whiskerRight_app]
  rw [← reassoc_of% hn]
  erw [hc]
  simp [leftDerivedUpperStarId, Functor.leftDerivedFunctorNatIso,
    leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion]

end IdAdjunction

/-! ### Base change along the trivial refinement -/

section BaseChangeAux

/-- The computation of the base change isomorphism `j_! ⋙ Lj^* ≅ L(𝟙)^* ⋙ (𝟙)_!` against the
unit of `j_! ⊣ Lj^*`, for abstract functors: `BC` is inverse to the exchange morphism of the
pullback square comparison `θ`, the adjunction `iS ⊣ Li` is identified with the identity
adjunction by `ι` and `ui'` (`hF4`), and `θ` is compatible with the identity isomorphisms
(`hθ`). -/
lemma clopen_baseChange_aux {DU DX : Type*} [Category DU] [Category DX]
    {jS : DU ⥤ DX} {Lj : DX ⥤ DU} (a : jS ⊣ Lj) {iS Li L1 : DU ⥤ DU} (a' : iS ⊣ Li)
    (ι : iS ≅ 𝟭 DU) (ui' : Li ≅ 𝟭 DU) (ui : L1 ≅ 𝟭 DU) (θ : Lj ⋙ L1 ≅ Lj ⋙ Li)
    (BC : jS ⋙ Lj ≅ L1 ⋙ iS) (hBC : BC.inv = Adjunction.exchangeLeft a a' θ)
    (hF4 : ∀ W, ι.inv.app (Li.obj W) ≫ a'.counit.app W = ui'.hom.app W)
    (hθ : ∀ Z, ui.inv.app (Lj.obj Z) ≫ θ.hom.app Z ≫ ui'.hom.app (Lj.obj Z) = 𝟙 _) (N : DU) :
    a.unit.app N ≫ BC.hom.app N ≫ ι.hom.app (L1.obj N) = ui.inv.app N := by
  have h : ui.inv.app N ≫ ι.inv.app (L1.obj N) ≫ BC.inv.app N = a.unit.app N := by
    rw [hBC, Adjunction.exchangeLeft_app]
    have n1 := ι.inv.naturality (L1.map (a.unit.app N))
    have n2 := ui.inv.naturality (a.unit.app N)
    have n3 := ι.inv.naturality (θ.hom.app (jS.obj N))
    simp only [Functor.id_map, Functor.comp_obj, Functor.id_obj] at n1 n2 n3
    rw [← reassoc_of% n1, ← reassoc_of% n2, ← reassoc_of% n3, hF4, hθ]
    simp
  rw [← h]
  simp

end BaseChangeAux

/-! ### The refinement of an open and proper immersion -/

section Clopen

variable {k : Type u} [Field k] {U X : Over (Spec (.of k))} (j : U ⟶ X) [IsOpenImmersion j.left]
  [IsProper j.left]

/-- The open immersion of the trivial compactification `U ⟶[𝟙] U ⟶[j] X` of the proper `j` is an
isomorphism. -/
instance isIso_ofIsProper_overI : IsIso (Compactification.ofIsProper j.left).overI := by
  have : IsIso ((Over.forget _).map (Compactification.ofIsProper j.left).overI) :=
    inferInstanceAs (IsIso (𝟙 U.left))
  exact isIso_of_reflects_iso _ (Over.forget _)

/-- The morphism `j` from the middle object of the compactification `U ⟶[𝟙] U ⟶[j] X` to `X`. -/
noncomputable def openImmersionProperRefinementHom :
    (Compactification.ofIsProper j.left).overObj ⟶ X :=
  Over.homMk j.left (by
    change j.left ≫ X.hom = j.left ≫ X.hom
    rfl)

instance : IsProper (openImmersionProperRefinementHom j).left :=
  inferInstanceAs (IsProper j.left)

omit [IsOpenImmersion j.left] in
lemma openImmersionProperRefinementHom_comp_id :
    openImmersionProperRefinementHom j ≫ 𝟙 X = (Compactification.ofIsProper j.left).overG := by
  ext
  simp [openImmersionProperRefinementHom, Compactification.overG]
  rfl

lemma isPullback_openImmersionProperRefinementHom :
    IsPullback (𝟙 U) (Compactification.ofIsProper j.left).overI j
      (openImmersionProperRefinementHom j) := by
  have : Mono j := Over.mono_of_mono_left j
  refine (IsKernelPair.id_of_mono j).of_iso (Iso.refl _) (Iso.refl _)
    (asIso (Compactification.ofIsProper j.left).overI) (Iso.refl _) (by simp) (by simp)
    (by simp) ?_
  ext
  simp [openImmersionProperRefinementHom, Compactification.overI]
  rfl

/-- The refinement `j` of the compactification `U ⟶[j] X ⟶[𝟙] X` of `j` by the compactification
`U ⟶[𝟙] U ⟶[j] X`. -/
noncomputable def openImmersionProperRefinement :
    Compactification.OverRefinement (Compactification.ofIsProper j.left)
      (Compactification.ofIsOpenImmersion j.left) where
  hom := openImmersionProperRefinementHom j ≫ openImmersionCompactificationHom j
  hom_overG := by
    rw [Category.assoc, openImmersionCompactificationHom_comp_overG,
      openImmersionProperRefinementHom_comp_id]
  isPullback := by
    simpa using (isPullback_openImmersionProperRefinementHom j).paste_horiz
      (isPullback_openImmersionCompactificationHom j)
  isProper := by
    rw [Over.comp_left]
    infer_instance

variable (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]

/-- For an open and proper immersion `j`, the composite `j_! ≅ Rj_! ≅ Rj_*` of the two
identifications of the lower shriek is the comparison along the refinement `j` of the
compactification `U ⟶[j] X ⟶[𝟙] X` by `U ⟶[𝟙] U ⟶[j] X`, up to the identifications
`R(𝟙 X)_* ≅ 𝟭` and `(𝟙 U)_! ≅ 𝟭`. -/
lemma boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_inv_comp :
    haveI := isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'_padicAlgCl ℓ
      (isPullback_openImmersionProperRefinementHom j)
    (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j).inv ≫
        (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ j).hom =
      (Functor.rightUnitor _).inv ≫
        Functor.whiskerLeft _ (boundedConstructibleLowerStarId ℓ X).inv ≫
        (boundedConstructibleLowerShriekRefinementIso' ℓ
          (isPullback_openImmersionProperRefinementHom j)
          (openImmersionProperRefinementHom_comp_id j)).hom ≫
        Functor.whiskerRight
          (boundedConstructibleOpenImmersionLowerShriekOfIsProperIso _ ℓ j).hom _ ≫
        (Functor.leftUnitor _).hom := by
  have := isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'_padicAlgCl ℓ
    (isPullback_openImmersionProperRefinementHom j)
  have := (openImmersionProperRefinement j).isProper
  have := isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'_padicAlgCl ℓ
    (openImmersionProperRefinement j).isPullback
  have hc := congrArg Iso.hom
    (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_trans ℓ
      (compactificationOverField j) (Compactification.ofIsOpenImmersion j.left)
      (Compactification.ofIsProper j.left))
  have hr := congrArg Iso.hom (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_eq
    ℓ (openImmersionProperRefinement j))
  rw [Iso.trans_hom] at hc
  rw [boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_eq,
    boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl,
    boundedConstructibleLowerShriekOfCompactificationOfIsProperIso]
  simp only [Iso.trans_inv, Iso.trans_hom, Category.assoc, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_hom]
  simp only [← hc, Category.assoc, Iso.inv_hom_id_assoc, hr]
  -- the proper-only `Rp_*` of the shriek and the general one agree definitionally
  rfl

/-- Composing with an identity and the image of an identity does nothing. -/
lemma id_comp_map_id_comp {C D : Type*} [Category C] [Category D] (F : C ⥤ D) (X : C) {Y : D}
    (c : F.obj X ⟶ Y) : 𝟙 (F.obj X) ≫ F.map (𝟙 X) ≫ c = c := by
  simp

omit [IsOpenImmersion j.left] in
/-- The adjunction `(𝟙 U)_! ⊣ L(𝟙 U)^*` on bounded constructible complexes attached to the
compactification `U ⟶[𝟙] U ⟶[j] X` is identified with the identity adjunction by
`(𝟙 U)_! ≅ 𝟭` and `L(𝟙 U)^* ≅ 𝟭`: `ι⁻¹ ≫ ε = u` on `L(𝟙 U)^*`. -/
lemma boundedConstructibleOpenImmersionLowerShriekOfIsProperIso_inv_app_comp_counit
    (W : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleOpenImmersionLowerShriekOfIsProperIso _ ℓ j).inv.app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (Compactification.ofIsProper j.left).overI).obj W) ≫
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
        (Profinite.padicAlgClRingObj ℓ) ℓ (Compactification.ofIsProper j.left).overI).counit.app W =
      (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ U).hom.app W := by
  ext1
  have h := (Adjunction.map_restrictFullyFaithful_counit_app
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction _
        (Compactification.ofIsProper j.left).overI.left).ofNatIsoRight
        (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion _
          (Compactification.ofIsProper j.left).overI.left).symm)
      (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
      (boundedConstructibleOpenImmersionLowerShriekCompatibility _ ℓ
        (Compactification.ofIsProper j.left).overI).symm
      (boundedConstructibleUpperStarCompatibility _ ℓ
        (Compactification.ofIsProper j.left).overI).symm W)
  have h1 (V : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
      ((boundedConstructibleOpenImmersionLowerShriekOfIsProperIso _ ℓ j).inv.app V).hom =
        (derivedOpenImmersionLowerShriekId _ U.left).inv.app V.obj := by
    simp only [Functor.id_obj, boundedConstructibleOpenImmersionLowerShriekOfIsProperIso,
      Functor.whiskeringRight_obj_obj, boundedConstructibleOpenImmersionLowerShriekCompatibility,
      ObjectProperty.liftCompιIso, Functor.FullyFaithful.preimageIso_inv, Iso.trans_inv,
      Iso.refl_inv, Functor.isoWhiskerLeft_inv, Iso.symm_inv, NatTrans.comp_app,
      Functor.FullyFaithful.whiskeringRight_preimage_app, NatTrans.id_app, Functor.comp_obj,
      ObjectProperty.ι_obj, ObjectProperty.lift_obj_obj,
      Functor.whiskerLeft_app, Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
      Category.id_comp, ObjectProperty.homMk_hom]
    exact Category.comp_id _
  rw [ObjectProperty.FullSubcategory.comp_hom, boundedConstructibleUpperStarId_hom_app_hom]
  have h' : ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) ℓ (Compactification.ofIsProper j.left).overI).counit.app
        W).hom =
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction _
        (Compactification.ofIsProper j.left).overI.left).ofNatIsoRight
        (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion _
          (Compactification.ofIsProper j.left).overI.left).symm).counit.app W.obj := by
    refine h.trans ?_
    simp only [boundedConstructibleOpenImmersionLowerShriekCompatibility,
      boundedConstructibleUpperStarCompatibility, ObjectProperty.liftCompιIso, Iso.symm_inv,
      Iso.refl_hom, NatTrans.id_app]
    exact id_comp_map_id_comp _ _ _
  have h2 := derivedOpenImmersionLowerShriekId_inv_app_comp_counit _ U.left W.obj
  erw [h1, h']
  exact h2

/-- The canonical map `j_! ⟶ Rj_*` of an open and proper immersion, assuming that the
adjunction `(𝟙 U)_! ⊣ L(𝟙 U)^*` of the compactification `U ⟶[𝟙] U ⟶[j] X` is identified with
the identity adjunction by `(𝟙 U)_! ≅ 𝟭` and `L(𝟙 U)^* ≅ 𝟭` (`hF4`). -/
theorem boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_clopen_of
    (hF4 : ∀ W, (boundedConstructibleOpenImmersionLowerShriekOfIsProperIso _ ℓ j).inv.app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (Compactification.ofIsProper j.left).overI).obj W) ≫
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
        (Profinite.padicAlgClRingObj ℓ) ℓ (Compactification.ofIsProper j.left).overI).counit.app W =
      (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ U).hom.app W)
    (M : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
        (Profinite.padicAlgClRingObj ℓ) ℓ j).unit.app M ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).map
        ((boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j).inv.app M ≫
          (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ j).hom.app M) ≫
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ
        j).counit.app M = 𝟙 M := by
  have := isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'_padicAlgCl ℓ
    (isPullback_openImmersionProperRefinementHom j)
  -- the objects attached to the middle object of `U ⟶[𝟙] U ⟶[j] X`, read on `U`
  let iS₀ := boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
    (Compactification.ofIsProper j.left).overI
  let iS : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
      Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
    iS₀
  let ι : iS ≅ 𝟭 _ := boundedConstructibleOpenImmersionLowerShriekOfIsProperIso _ ℓ j
  let a'₀ := boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
    (Profinite.padicAlgClRingObj ℓ) ℓ (Compactification.ofIsProper j.left).overI
  let a' : iS ⊣ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (𝟙 U) := a'₀
  let BC₀ := boundedConstructibleOpenImmersionLowerShriekBaseChangeIso'
    (Profinite.padicAlgClRingObj ℓ) ℓ (isPullback_openImmersionProperRefinementHom j)
  let BC : boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j ⋙
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j ≅
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (𝟙 U) ⋙ iS := BC₀
  let θ₀ := boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ
    (isPullback_openImmersionProperRefinementHom j).flip.toCommSq
  let θ : boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j ⋙
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (𝟙 U) ≅
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j ⋙
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (𝟙 U) := θ₀
  let Exch₀ := boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'
    ℓ (isPullback_openImmersionProperRefinementHom j)
  let Exch : boundedConstructibleLowerStar ℓ (𝟙 U) ⋙
      boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j ⟶
      iS ⋙ boundedConstructibleLowerStar ℓ j := Exch₀
  let comp₀ := boundedConstructibleLowerStarComp ℓ
    (openImmersionProperRefinementHom j) (𝟙 X)
  let comp : boundedConstructibleLowerStar ℓ j ⋙
      boundedConstructibleLowerStar ℓ (𝟙 X) ≅
      boundedConstructibleLowerStar ℓ j := comp₀
  have hBC : BC.inv = Adjunction.exchangeLeft
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j) a' θ := by
    simp only [BC, BC₀, a', a'₀, θ, θ₀]
    rw [boundedConstructibleOpenImmersionLowerShriekBaseChangeIso', Iso.symm_inv, asIso_hom,
      boundedConstructibleOpenImmersionLowerShriekBaseChange'_eq_exchangeLeft]
  have hθ1 (Z : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) : θ.hom.app Z = 𝟙 _ := by
    simp only [θ, θ₀, boundedConstructiblePullbackSquareComparison_hom_app]
    rw [← cancel_epi ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ
      (𝟙 U) j).hom.app Z), Iso.hom_inv_id_app_assoc]
    ext1
    simp [boundedConstructibleUpperStarComp_hom_app_hom, openImmersionProperRefinementHom,
      Compactification.ofIsProper]
    rfl
  have hF1 (N : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
      (boundedConstructibleLowerStarId ℓ X).inv.app
          ((boundedConstructibleLowerStar ℓ j).obj N) ≫
        comp.hom.app N = 𝟙 _ :=
    (boundedConstructibleLowerStarId_inv_app_comp_lowerStarComp_hom_app
      ℓ (openImmersionProperRefinementHom j) N).trans
      (eqToHom_refl _ _)
  have hF2 (N : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
      (boundedConstructibleLowerStarId ℓ U).inv.app N ≫
        (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ U).inv.app
          ((boundedConstructibleLowerStar ℓ (𝟙 U)).obj N) ≫
        (boundedConstructibleUpperStarLowerStarAdjunction ℓ
          (𝟙 U)).counit.app N = 𝟙 _ := by
    rw [← boundedConstructibleLowerStarId_hom_app, Iso.inv_hom_id_app]
  have hEx (N : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧) : Exch.app N =
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ
          j).unit.app ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ)
            ℓ j).obj ((boundedConstructibleLowerStar ℓ
              (𝟙 U)).obj N)) ≫
        (boundedConstructibleLowerStar ℓ j).map
          (BC.hom.app ((boundedConstructibleLowerStar ℓ
            (𝟙 U)).obj N)) ≫
        (boundedConstructibleLowerStar ℓ j).map
          (iS.map ((boundedConstructibleUpperStarLowerStarAdjunction
            ℓ (𝟙 U)).counit.app N)) := by
    simp [Exch, Exch₀, boundedConstructibleLowerStarOpenImmersionLowerShriekExchange',
      boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeUnitStep',
      boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeSquareStep',
      boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeCounitStep', BC, BC₀]
    rfl
  have hF3 := clopen_baseChange_aux
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j) a' ι
    (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ U)
    (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ U) θ BC hBC
    (fun W ↦ hF4 W) (fun Z ↦ by simp [hθ1 Z])
  have hφ := NatTrans.congr_app
    (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_inv_comp j ℓ) M
  rw [NatTrans.comp_app] at hφ
  have hφ₂ : (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j).inv.app M ≫
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ j).hom.app M =
      (boundedConstructibleLowerStarId ℓ X).inv.app
          ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).obj
            M) ≫
        (boundedConstructibleLowerStar ℓ (𝟙 X)).map
          ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).map
            ((boundedConstructibleLowerStarId ℓ U).inv.app M) ≫
            Exch.app M) ≫
        comp.hom.app (iS.obj M) ≫
        (boundedConstructibleLowerStar ℓ j).map (ι.hom.app M) := by
    rw [hφ]
    simp [boundedConstructibleLowerShriekRefinementIso', Exch, Exch₀, comp, comp₀, ι, iS, iS₀]
    rfl
  rw [hφ₂]
  exact clopen_comparison_aux
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ j)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (𝟙 U))
    (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ U)
    (boundedConstructibleLowerStarId ℓ U) ι BC
    (boundedConstructibleLowerStarId ℓ X) comp Exch hF1 hF2 hF3
    hEx M

end Clopen

end AlgebraicGeometry.ProEtale.CondensedRing
