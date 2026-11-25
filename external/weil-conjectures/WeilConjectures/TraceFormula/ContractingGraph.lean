/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.ContractingLocalTerm
public import WeilConjectures.TraceFormula.LocalTermPoint
public import WeilConjectures.TraceFormula.PieceAdditivity

/-!

# Local terms of contracting graph correspondences

Let `c = (𝟙, h)` be the graph correspondence of an endomorphism `h : X ⟶ X` with coefficient map
`v : Lh^* K ⟶ K`, contracting at a rational point `x` fixed by `h`. By Varshavsky's theorem for
contracting correspondences (`Correspondence.restrict_traceClass_eq_pushforward_of_isContractingAt`)
the trace class on an open and closed subscheme `B` of the fixed locus with underlying set `{x}`
is the pushforward of the trace class of the restricted coefficient map `u_Z : K_x ⟶ K_x`
(`Correspondence.contractingStalkMap`). For a graph the exceptional leg is the identity, the base
change of `R(𝟙)_!` along `x` is the identity up to the identity isomorphisms
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekBaseChange_padicAlgCl_app_of_id`), and so
`u_Z` is the stalk map `v_x` (`Correspondence.contractingStalkMap_ofGraph`). Hence the local term
at `x` is `tr(v_x)` (blueprint `corollary-contracting-local-terms-point`, item 1; Varshavsky, Thm.
2.1.3, Fujiwara's theorem).

## Main statements

- `ProEtale.CondensedRing.Correspondence.localTerm_traceClass_eq_integral_of_isContractingAt`:
  at a contracting fixed point the local term is the integral of the trace class of `u_Z`.
- `ProEtale.CondensedRing.Correspondence.contractingStalkMap_ofGraph`: for a graph, `u_Z` is the
  stalk map.
- `Correspondence.restrict_traceClass_ofGraph_eq_pushforward_of_isContractingAt`:
  Varshavsky's theorem for graphs, through the additivity of trace classes for graphs.
- `ProEtale.CondensedRing.Correspondence.localTerm_traceClass_ofGraph_eq_trace_of_isContractingAt`:
  the local term of a contracting graph correspondence is the trace of the stalk map.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

/-! ### The mate of a square of identities -/

section Abstract

variable {A B : Type*} [Category A] [Category B] {L : A ⥤ B} {R : B ⥤ A} {G : A ⥤ A}
  {H : B ⥤ B}

/-- Let `L ⊣ R` be an adjunction and `G ≅ 𝟭`, `H ≅ 𝟭` endofunctors. If the 2-square
`β : R ⋙ G ⟶ H ⋙ R` is the identity under these identifications, so is its mate
`G ⋙ L ⟶ L ⋙ H`. -/
lemma mateEquiv_symm_app_of_isoId (adj : L ⊣ R) (eG : G ≅ 𝟭 A) (eH : H ≅ 𝟭 B)
    (β : TwoSquare R H G R)
    (hβ : ∀ N, β.app N ≫ R.map (eH.hom.app N) = eG.hom.app (R.obj N)) (M : A) :
    ((mateEquiv adj adj).symm β).app M =
      L.map (eG.hom.app M) ≫ eH.inv.app (L.obj M) := by
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  refine (unit_mateEquiv_symm adj adj β M).symm.trans ?_
  rw [← cancel_mono (R.map (eH.hom.app (L.obj M))), Category.assoc, Category.assoc, hβ,
    ← R.map_comp, Category.assoc, Iso.inv_hom_id_app]
  dsimp only [Functor.id_obj]
  rw [Category.comp_id]
  have h₁ := eG.hom.naturality (adj.unit.app M)
  have h₂ := adj.unit.naturality (eG.hom.app M)
  dsimp only [Functor.id_map, Functor.id_obj, Functor.comp_map, Functor.comp_obj] at h₁ h₂
  rw [h₁, h₂]

end Abstract

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-! ### Compact-support base change along the identity -/

section BaseChange

variable {X X' : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]

variable (ℓ) in
/-- The composition isomorphism `Rg_! ⋙ R(𝟙)_! ≅ R(𝟙)_! ⋙ Rg_!` of the square
`g ≫ 𝟙 = 𝟙 ≫ g` is the identity, up to the identity isomorphisms `R(𝟙)_! ≅ 𝟭`. -/
lemma boundedConstructibleLowerShriekSquareIso_id_hom_app (g : X' ⟶ X)
    (w : g ≫ 𝟙 X = 𝟙 X' ≫ g) (N : Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ w).hom.app N ≫
        (boundedConstructibleLowerShriek ℓ g).map
          ((boundedConstructibleLowerShriekId ℓ X').hom.app N) =
      (boundedConstructibleLowerShriekId ℓ X).hom.app
        ((boundedConstructibleLowerShriek ℓ g).obj N) := by
  rw [← cancel_epi ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ g (𝟙 X)).hom.app N)]
  simp only [boundedConstructibleLowerShriekSquareIso_padicAlgCl, boundedConstructibleLowerShriekId,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app, Category.assoc,
    Iso.hom_inv_id_app_assoc]
  rw [boundedConstructibleLowerShriekComp_padicAlgCl_id_left,
    boundedConstructibleLowerShriekComp_padicAlgCl_id_right, eqToHom_trans]

variable (ℓ) in
/-- **Compact-support base change along a square of identities.** For a cartesian square
`g' ≫ 𝟙 = 𝟙 ≫ g` (so `g' = g`) with `g` and `g'` proper, the base change
`Ex_! : R(𝟙)_! ⋙ Lg^* ⟶ Lg'^* ⋙ R(𝟙)_!` is the identity, up to the identity isomorphisms
`R(𝟙)_! ≅ 𝟭` and `Lg^* = Lg'^*`. -/
lemma boundedConstructibleLowerShriekBaseChange_padicAlgCl_app_of_id {g g' : X' ⟶ X}
    (sq : IsPullback g' (𝟙 X') (𝟙 X) g) [IsProper g.left] [IsProper g'.left]
    (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).app M =
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).map
          ((boundedConstructibleLowerShriekId ℓ X).hom.app M) ≫
        eqToHom (by obtain rfl : g' = g := (by simpa using sq.w); rfl) ≫
        (boundedConstructibleLowerShriekId ℓ X').inv.app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g').obj M) := by
  obtain rfl : g' = g := by simpa using sq.w
  rw [boundedConstructibleLowerShriekBaseChange_padicAlgCl_eq_mateEquiv, eqToHom_refl,
    Category.id_comp]
  exact mateEquiv_symm_app_of_isoId _ _ _ _
    (boundedConstructibleLowerShriekSquareIso_id_hom_app ℓ g' sq.w) M

end BaseChange

namespace Correspondence

variable {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}

/-! ### The local term at a contracting point -/

/-- **The local term at a contracting point** (blueprint
`theorem-contracting-correspondences-local-terms` for `Z = {c₁(y)}`, Varshavsky, Thm. 2.1.3): if `c`
is contracting at the fixed point `y` and `B` is an open and closed subscheme of the fixed locus,
proper over `s`, with underlying set `{y}`, the local term along `B` is the integral of the trace
class of the restricted coefficient map `u_Z` on the stalk `L(y ≫ c₁)^* K` over the point. -/
theorem localTerm_traceClass_eq_integral_of_isContractingAt {c : Correspondence ℓ K}
    (F : c.FixedLocus) (y : RationalPoint c.C) (hc : c.IsContractingAt y)
    {B : Over (Spec (.of k))} [QuasiCompact B.hom] [IsProper B.hom] (j : B ⟶ F.F)
    [IsOpenImmersion j.left] [IsClosedImmersion j.left]
    (hB : Set.range j.left.base =
      {(F.liftPoint y hc.comp_c₁_eq_comp_c₂).left.base (default : Spec (.of k))}) :
    (c.traceClass F).localTerm j =
      ((ofEnd _ (contractingStalkMap hc)).traceClass (fixedLocusOfEnd _)).integral :=
  localTerm_traceClass_eq_integral_of_restrict_eq F _ j hB _ fun e _ he ↦
    restrict_traceClass_eq_pushforward_of_isContractingAt c F hc j e he hB

/-- The trace class of the diagonal correspondence of an endomorphism `f` of `M` which is
conjugate, along an equality `M = N`, to an endomorphism `g` of `N` is the trace class of `g`. -/
lemma traceClass_ofEnd_of_eq_eqToHom {M N : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (e : M = N) {f : M ⟶ M} {g : N ⟶ N} (hfg : f = eqToHom e ≫ g ≫ eqToHom e.symm) :
    (ofEnd M f).traceClass (fixedLocusOfEnd f) = (ofEnd N g).traceClass (fixedLocusOfEnd g) := by
  subst e hfg
  rw [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- The integral of the trace class of the diagonal correspondence of an endomorphism `f` of `M`
which is conjugate, along an equality `M = N`, to an endomorphism `g` of a dualizable `N` is the
trace of `g` (point normalization). -/
lemma integral_traceClass_ofEnd_of_eq_eqToHom
    {M N : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (e : M = N) {f : M ⟶ M} {g : N ⟶ N} (hfg : f = eqToHom e ≫ g ≫ eqToHom e.symm)
    [HasRightDual N] :
    ((ofEnd M f).traceClass (fixedLocusOfEnd f)).integral = End.of (trace g) := by
  rw [traceClass_ofEnd_of_eq_eqToHom e hfg]
  exact integral_traceClass_ofEnd g

/-! ### Graph correspondences -/

/-- The pullbacks along equal morphisms are related by the cast. -/
lemma boundedConstructibleUpperStar_map_comp_eqToHom {P : Over (Spec (.of k))}
    [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom] {g g' : P ⟶ X}
    (e : g = g') {M N : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (f : M ⟶ N) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).map f ≫
        eqToHom (by rw [e]) =
      eqToHom (by rw [e]) ≫
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g').map f := by
  subst e
  simp

/-- The right adjunct for `R(𝟙)_! ⊣ R(𝟙)^!`, followed by `R(𝟙)^! ≅ 𝟭`, is precomposition with
`R(𝟙)_! ≅ 𝟭`. -/
lemma boundedConstructibleUpperShriekAdjunction_id_homEquiv_comp
    {M N : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (f : (boundedConstructibleLowerShriek ℓ (𝟙 X)).obj M ⟶ N) :
    (boundedConstructibleUpperShriekAdjunction ℓ
        (𝟙 X)).homEquiv _ _ f ≫ (boundedConstructibleUpperShriekId ℓ X).hom.app N =
      (boundedConstructibleLowerShriekId ℓ X).inv.app M ≫ f := by
  obtain ⟨g, rfl⟩ := ((boundedConstructibleUpperShriekAdjunction ℓ
    (𝟙 X)).homEquiv M N).symm.surjective f
  have hn := (boundedConstructibleLowerShriekId ℓ X).hom.naturality g
  dsimp only [Functor.id_map, Functor.id_obj] at hn
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_counit,
    boundedConstructibleUpperShriekAdjunction_id_counit_app, reassoc_of% hn,
    Iso.inv_hom_id_app_assoc]

set_option backward.isDefEq.respectTransparency true in
variable (K) in
/-- **The restricted coefficient map of a graph is the stalk map**: for the graph correspondence
`(𝟙, h)` of `v : Lh^* K ⟶ K`, contracting at the rational point `x`, the restricted coefficient
map `u_Z` of Varshavsky's theorem is the stalk map `v_x : K_x ⟶ K_x`, up to `x ≫ 𝟙 = x`. -/
theorem contractingStalkMap_ofGraph (h : X ⟶ X)
    (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h).obj K ⟶ K)
    {x : RationalPoint X} (hc : (ofGraph K h v).IsContractingAt x) :
    contractingStalkMap hc =
      eqToHom (congrArg
          (fun g ↦ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).obj K)
          (Category.comp_id x :
            @CategoryStruct.comp _ _ (point k) (ofGraph K h v).C X x
              (ofGraph K h v).c₁ = x)) ≫
        graphStalkMap K h v x (comp_eq_of_isContractingAt_ofGraph hc) ≫
        eqToHom (congrArg
          (fun g ↦ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).obj K)
          (Category.comp_id x :
            @CategoryStruct.comp _ _ (point k) (ofGraph K h v).C X x
              (ofGraph K h v).c₁ = x).symm) := by
  have hx := comp_eq_of_isContractingAt_ofGraph hc
  have sq : IsPullback x (𝟙 (point k)) (𝟙 X) (x ≫ 𝟙 X) := hc.isPullback
  have := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq
  unfold contractingStalkMap restrictedStalkMap graphStalkMap
  change eqToHom (congrArg
          (fun g ↦ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).obj K)
        (show x ≫ 𝟙 X = x ≫ h by rw [hx, Category.comp_id])) ≫
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ x h).hom.app K ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).map
        (v ≫ (boundedConstructibleUpperShriekId ℓ X).inv.app K) ≫
      (boundedConstructibleUpperShriekAdjunction ℓ
        (𝟙 (point k))).homEquiv
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj
          ((boundedConstructibleUpperShriek ℓ (𝟙 X)).obj K))
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (x ≫ 𝟙 X)).obj K)
        ((asIso (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq)).inv.app
            ((boundedConstructibleUpperShriek ℓ (𝟙 X)).obj K) ≫
          (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (x ≫ 𝟙 X)).map
            ((boundedConstructibleUpperShriekAdjunction ℓ
              (𝟙 X)).counit.app K)) ≫
      (boundedConstructibleUpperShriekId ℓ (point k)).hom.app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (x ≫ 𝟙 X)).obj K) = _
  have hinv : (asIso (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ
      sq)).inv.app ((boundedConstructibleUpperShriek ℓ
        (𝟙 X)).obj K) =
      (boundedConstructibleLowerShriekId ℓ (point k)).hom.app _ ≫ eqToHom (by
        rw [Category.comp_id]; rfl) ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (x ≫ 𝟙 X)).map
        ((boundedConstructibleLowerShriekId ℓ X).inv.app _) := by
    rw [← cancel_epi ((asIso (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ
      sq)).hom.app _), Iso.hom_inv_id_app, asIso_hom,
      boundedConstructibleLowerShriekBaseChange_padicAlgCl_app_of_id]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp, ← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
    rfl
  rw [boundedConstructibleUpperShriekAdjunction_id_homEquiv_comp]
  rw [hinv]
  rw [boundedConstructibleUpperShriekAdjunction_id_counit_app]
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc]
  have e₁ := ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (x ≫ 𝟙 X)).mapIso
    ((boundedConstructibleLowerShriekId ℓ X).app
      ((boundedConstructibleUpperShriek ℓ (𝟙 X)).obj
        K))).inv_hom_id_assoc
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (x ≫ 𝟙 X)).map
      ((boundedConstructibleUpperShriekId ℓ X).hom.app K))
  have e₂ := ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (x ≫ 𝟙 X)).mapIso
    ((boundedConstructibleUpperShriekId ℓ X).app K)).inv_hom_id
  have e₃ := boundedConstructibleUpperStar_map_comp_eqToHom (Category.comp_id x).symm
    ((boundedConstructibleUpperShriekId ℓ X).inv.app K)
  simp only [Functor.mapIso_inv, Functor.mapIso_hom, Iso.app_inv, Iso.app_hom] at e₁ e₂
  simp only [e₁, reassoc_of% e₃, e₂]
  simp only [eqToHom_trans_assoc]
  dsimp only [Functor.id_obj]
  simp only [Category.comp_id]

/-- **Contracting graph correspondences and local terms** (blueprint
`theorem-contracting-correspondences-local-terms` for the graph correspondence `(𝟙, h)` and
`Z = {x}`; Varshavsky, Thm. 2.1.3): if the graph correspondence `(𝟙, h)` with coefficient map
`v : Lh^* K ⟶ K` is contracting at the fixed rational point `x`, and `B` is an open and closed
subscheme of the fixed locus, proper over `s`, with underlying set `{x}` and point `e : s ⟶ B`,
the restriction of the trace class to `B` is the pushforward along `e` of the trace class of
the restricted coefficient map `u_Z`, which is the stalk map `v_x` (`contractingStalkMap_ofGraph`).

This is the special case `c = (𝟙, h)` of `restrict_traceClass_eq_pushforward_of_isContractingAt`,
proved through the additivity of trace classes for graphs (`traceClass_ofGraph_eq_add`) instead of
the additivity for arbitrary correspondences (`traceClass_eq_add_of_isPullback`). It keeps
the graph case, which carries every current user, independent of the mate description of the
compact-support base change (`boundedConstructibleLowerShriekBaseChange_padicAlgCl_eq_mateEquiv`)
that the general closed piece needs. The proof: the
trace class is the sum of the trace classes of `u^Z` on `K^Z = Rx_* Lx^* K` and `u^U` on
`K^U = j_! Lj^* K`; the first is the pushforward of the trace class of `v_x` by proper pushforward
compatibility (`ProperPushforwardDiagram.traceClassPushforward_eq`), and the second vanishes on
`B` since the stalk of `K^U` at `x` is zero (`restrict_traceClass_eq_zero_of_isContractingAt`). -/
theorem restrict_traceClass_ofGraph_eq_pushforward_of_isContractingAt (h : X ⟶ X)
    (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h).obj K ⟶ K)
    (F : (ofGraph K h v).FixedLocus) {x : RationalPoint X}
    (hc : (ofGraph K h v).IsContractingAt x) {B : Over (Spec (.of k))} [QuasiCompact B.hom]
    [IsProper B.hom] (j : B ⟶ F.F) [IsOpenImmersion j.left] [IsClosedImmersion j.left]
    (e : point k ⟶ B) [IsProper e.left] (he : e ≫ j = F.liftPoint x hc.comp_c₁_eq_comp_c₂)
    (hB : Set.range j.left.base =
      {(F.liftPoint x hc.comp_c₁_eq_comp_c₂).left.base (default : Spec (.of k))}) :
    ((ofGraph K h v).traceClass F).restrict j = BorelMooreSection.pushforward e
      ((ofEnd _ (contractingStalkMap hc)).traceClass (fixedLocusOfEnd _)) := by
  have hx := comp_eq_of_isContractingAt_ofGraph hc
  have hc' : ((ofGraph K h v).withCoeff (pointOpenPiece K x)
      (graphOpenPieceCoeff K v hx ≫
        (boundedConstructibleUpperShriekId ℓ X).inv.app _)).IsContractingAt x :=
    ⟨hc.1, hc.2, hc.3⟩
  have hK : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (x ≫ 𝟙 X)).obj (pointOpenPiece K x)) := by
    refine isZero_boundedConstructibleUpperStar_obj_openImmersionLowerShriek _ ℓ
      (pointComplι x) _ ?_ _
    rw [Category.comp_id]
    exact (isCompl_range_pointComplι x).disjoint
  have hU : (F.traceClassWithCoeff _ (graphOpenPieceCoeff K v hx ≫
      (boundedConstructibleUpperShriekId ℓ X).inv.app _)).restrict j = 0 :=
    restrict_traceClass_eq_zero_of_isContractingAt
      ((ofGraph K h v).withCoeff (pointOpenPiece K x)
        (graphOpenPieceCoeff K v hx ≫ (boundedConstructibleUpperShriekId ℓ X).inv.app _))
      (F.withCoeff _ _) hc' j hB hK
  let P := graphClosedPieceDiagram K v hx
  let Fc := fixedLocusOfEnd (graphStalkMap K h v x hx)
  let Fb : P.pushforward.FixedLocus := F.withCoeff _ (graphClosedPieceCoeff K v hx)
  have : IsProper (e ≫ j).left := by
    rw [Over.comp_left]
    infer_instance
  have hfix : P.fixMap Fc Fb = e ≫ j := by
    rw [he]
    refine Fb.hom_ext ?_
    rw [P.fixMap_ι]
    exact (Category.id_comp x).trans (F.liftPoint_ι x _).symm
  have hZ := P.traceClassPushforward_eq Fc Fb
  rw [ProperPushforwardDiagram.traceClassPushforward, BorelMooreSection.pushforward_congr hfix,
    ← BorelMooreSection.pushforward_comp] at hZ
  rw [traceClass_ofGraph_eq_add K v hx F, BorelMooreSection.restrict_add, hU, add_zero]
  change (P.pushforward.traceClass Fb).restrict j = _
  rw [← hZ, BorelMooreSection.restrict_pushforward_self]
  exact congrArg _ (traceClass_ofEnd_of_eq_eqToHom _ (contractingStalkMap_ofGraph K h v hc)).symm

/-- **Local terms of contracting graph correspondences** (blueprint
`corollary-contracting-local-terms-point`, item 1, for correspondences with exceptional leg
`c₁ = 𝟙`; Varshavsky, Thm. 2.1.3): if the graph correspondence `(𝟙, h)` with coefficient map
`v : Lh^* K ⟶ K` is contracting at the fixed rational point `x`, and `B` is an open and closed
subscheme of the fixed locus, proper over `s`, with underlying set `{x}`, then the local term along
`B` is the trace of the stalk map `v_x : K_x ⟶ K_x`. No invertibility of `v` is required.

By Varshavsky's theorem for graphs
(`restrict_traceClass_ofGraph_eq_pushforward_of_isContractingAt`) the local term is the integral
of the trace class of the restricted coefficient map `u_Z`, which is the stalk map `v_x`
(`contractingStalkMap_ofGraph`), and the trace class of an endomorphism of the point integrates
to its trace (point normalization). -/
theorem localTerm_traceClass_ofGraph_eq_trace_of_isContractingAt (h : X ⟶ X)
    (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h).obj K ⟶ K)
    (F : (ofGraph K h v).FixedLocus) (x : RationalPoint X)
    (hc : (ofGraph K h v).IsContractingAt x) {B : Over (Spec (.of k))} [QuasiCompact B.hom]
    [IsProper B.hom] (j : B ⟶ F.F) [IsOpenImmersion j.left] [IsClosedImmersion j.left]
    (hB : Set.range j.left.base =
      {(F.liftPoint x hc.comp_c₁_eq_comp_c₂).left.base (default : Spec (.of k))})
    [HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K)] :
    ((ofGraph K h v).traceClass F).localTerm j =
      End.of (trace (graphStalkMap K h v x (comp_eq_of_isContractingAt_ofGraph hc))) := by
  rw [localTerm_traceClass_eq_integral_of_restrict_eq F hc.comp_c₁_eq_comp_c₂ j hB _
    fun e _ he ↦ restrict_traceClass_ofGraph_eq_pushforward_of_isContractingAt h v F hc j e he hB]
  exact integral_traceClass_ofEnd_of_eq_eqToHom _ (contractingStalkMap_ofGraph K h v hc)

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
