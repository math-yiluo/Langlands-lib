/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.GaloisLayerAction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.NonFlatPullFac

/-!
# Extension of scalars commutes with the derived unit and the unit transport

Let `a : Λ ⟶ Λ'` be a morphism of commutative condensed rings and write `T = L(Ext_a)` for the
derived extension of scalars. For `p : G ⟶ T₀` and `q : G ⟶ S`, the comparison
`ProEtale.CondensedRing.derivedPushPullExtendScalarsHom a p q K`
```
T (Rp_* Lq^* K) ⟶ Rp_* T (Lq^* K) ≅ Rp_* Lq^* (T K)
```
is the push comparison `ProEtale.CondensedRing.derivedUpperStarExtendScalarsPushHom a p` followed
by the pull isomorphism `ProEtale.CondensedRing.derivedUpperStarExtendScalarsIso a q`. We show:

* `ProEtale.CondensedRing.map_unit_comp_derivedPushPullExtendScalarsHom`: it carries `T` of the
  unit of `Lq^* ⊣ Rq_*` to the unit of `Lq^* ⊣ Rq_*` with coefficients `Λ'` (the push comparison
  is the mate of the inverse of the pull isomorphism);
* `ProEtale.CondensedRing.derivedUpperStarExtendScalarsPushHom_comp_app`: the push comparisons
  are compatible with the composition isomorphisms `Rp_* ⋙ Rq_* ≅ R(p ≫ q)_*`; this is the mate
  of the compatibility `ProEtale.CondensedRing.derivedUpperStarExtendScalarsIsoCompCoherence` of
  the pull isomorphisms with the composition of derived pullbacks, through the abstract
  `CategoryTheory.mateEquiv_conjugateIsoEquiv_comp_app`;
* `ProEtale.CondensedRing.map_derivedUnitTransport_comp_derivedPushPullExtendScalarsHom`: it
  commutes with the unit transports `ProEtale.CondensedRing.derivedUnitTransport` along any
  `s : G' ⟶ G`;
* `ProEtale.CondensedRing.isIso_derivedPushPullExtendScalarsHom`: it is an isomorphism as soon as
  the push comparison is, and the arrow-isomorphism corollaries
  `ProEtale.CondensedRing.arrowIsoMapUnit` and
  `ProEtale.CondensedRing.arrowIsoMapDerivedUnitTransport`.

-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory

variable {C₁ C₂ C₃ C₁' C₂' C₃' : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
  [Category* C₁'] [Category* C₂'] [Category* C₃']
  {L₁₂ : C₁ ⥤ C₂} {R₂₁ : C₂ ⥤ C₁} {L₂₃ : C₂ ⥤ C₃} {R₃₂ : C₃ ⥤ C₂}
  {L₁₃ : C₁ ⥤ C₃} {R₃₁ : C₃ ⥤ C₁}
  {L₁₂' : C₁' ⥤ C₂'} {R₂₁' : C₂' ⥤ C₁'} {L₂₃' : C₂' ⥤ C₃'} {R₃₂' : C₃' ⥤ C₂'}
  {L₁₃' : C₁' ⥤ C₃'} {R₃₁' : C₃' ⥤ C₁'}
  (adj₁₂ : L₁₂ ⊣ R₂₁) (adj₂₃ : L₂₃ ⊣ R₃₂) (adj₁₃ : L₁₃ ⊣ R₃₁)
  (adj₁₂' : L₁₂' ⊣ R₂₁') (adj₂₃' : L₂₃' ⊣ R₃₂') (adj₁₃' : L₁₃' ⊣ R₃₁')
  {T₁ : C₁ ⥤ C₁'} {T₂ : C₂ ⥤ C₂'} {T₃ : C₃ ⥤ C₃'}
  (e₁₂ : L₁₂ ⋙ T₂ ≅ T₁ ⋙ L₁₂') (e₂₃ : L₂₃ ⋙ T₃ ≅ T₂ ⋙ L₂₃') (e₁₃ : L₁₃ ⋙ T₃ ≅ T₁ ⋙ L₁₃')
  (c : L₁₃ ≅ L₁₂ ⋙ L₂₃) (c' : L₁₃' ≅ L₁₂' ⋙ L₂₃')

/-- **Mates of compatible isomorphisms are compatible with the conjugate composition
isomorphisms.** Let `e_{ij} : L_{ij} ⋙ T_j ≅ T_i ⋙ L'_{ij}` be isomorphisms compatible with
composition isomorphisms `c : L₁₃ ≅ L₁₂ ⋙ L₂₃` and `c'`. Then the mates
`β_{ij} : R_{ji} ⋙ T_i ⟶ T_j ⋙ R'_{ji}` of the inverses of `e_{ij}` are compatible with the
conjugates `R₃₂ ⋙ R₂₁ ≅ R₃₁` of `c` and `c'`. -/
lemma mateEquiv_conjugateIsoEquiv_comp_app
    (h : ∀ M, e₁₃.hom.app M ≫ c'.hom.app (T₁.obj M) =
      T₃.map (c.hom.app M) ≫ e₂₃.hom.app (L₁₂.obj M) ≫ L₂₃'.map (e₁₂.hom.app M))
    (N : C₃) :
    T₁.map ((conjugateIsoEquiv (adj₁₂.comp adj₂₃) adj₁₃ c).hom.app N) ≫
        (mateEquiv adj₁₃ adj₁₃' (.mk _ _ _ _ e₁₃.inv)).app N =
      (mateEquiv adj₁₂ adj₁₂' (.mk _ _ _ _ e₁₂.inv)).app (R₃₂.obj N) ≫
        R₂₁'.map ((mateEquiv adj₂₃ adj₂₃' (.mk _ _ _ _ e₂₃.inv)).app N) ≫
        (conjugateIsoEquiv (adj₁₂'.comp adj₂₃') adj₁₃' c').hom.app (T₃.obj N) := by
  have key : (TwoSquare.mk _ _ _ _ e₁₃.inv : TwoSquare T₁ L₁₃ L₁₃' T₃) =
      ((TwoSquare.vComp (TwoSquare.mk _ _ _ _ e₁₂.inv : TwoSquare T₁ L₁₂ L₁₂' T₂)
        (TwoSquare.mk _ _ _ _ e₂₃.inv : TwoSquare T₂ L₂₃ L₂₃' T₃)).whiskerRight
          c'.hom).whiskerLeft c.inv := by
    ext M
    rw [← cancel_epi (e₁₃.hom.app M)]
    dsimp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vComp,
      TwoSquare.mk]
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp, Category.assoc,
      Functor.comp_obj, Iso.hom_inv_id_app]
    rw [reassoc_of% h]
    simp [← Functor.map_comp, ← Functor.map_comp_assoc]
  have := NatTrans.congr_app (
    (congrArg (mateEquiv adj₁₃ adj₁₃') key)) N
  rw [conjugateEquiv_mateEquiv_vcomp adj₁₃ (adj₁₂.comp adj₂₃) adj₁₃',
    mateEquiv_conjugateEquiv_vcomp (adj₁₂.comp adj₂₃) (adj₁₂'.comp adj₂₃') adj₁₃',
    mateEquiv_hcomp] at this
  rw [this]
  dsimp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp, Category.comp_id,
    Functor.comp_obj]
  rw [← conjugateIsoEquiv_apply_inv]
  refine ((T₁.mapIso ((conjugateIsoEquiv (adj₁₂.comp adj₂₃) adj₁₃ c).app N)).hom_inv_id_assoc
    _).trans ?_
  rw [conjugateIsoEquiv_apply_hom, Category.assoc]

/-- The comparison `T R L ⟶ R' T L ≅ R' L' T` built from the mate of the inverse of an
isomorphism `e : L ⋙ T' ≅ T ⋙ L'` carries `T` of the unit of `L ⊣ R` to the unit of `L' ⊣ R'`. -/
lemma map_unit_comp_mateEquiv_app_comp {C D C' D' : Type*} [Category* C] [Category* D]
    [Category* C'] [Category* D'] {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    {T : C ⥤ C'} {T' : D ⥤ D'} (adj : L ⊣ R) (adj' : L' ⊣ R') (e : L ⋙ T' ≅ T ⋙ L') (K : C) :
    T.map (adj.unit.app K) ≫ (mateEquiv adj adj' (.mk _ _ _ _ e.inv)).app (L.obj K) ≫
        R'.map (e.hom.app K) =
      adj'.unit.app (T.obj K) := by
  rw [← Category.assoc, unit_mateEquiv, Category.assoc, ← R'.map_comp]
  simp

section UnitTransport

variable {CS CG' CG CT CS' CG'' CGp CT' : Type*} [Category* CS] [Category* CG'] [Category* CG]
  [Category* CT] [Category* CS'] [Category* CG''] [Category* CGp] [Category* CT']
  {Lq : CS ⥤ CG'} {Ls : CG' ⥤ CG} {Lsq : CS ⥤ CG} {Lp : CT ⥤ CG'} {Rp : CG' ⥤ CT}
  {Rs : CG ⥤ CG'} {Lsp : CT ⥤ CG} {Rsp : CG ⥤ CT}
  {Lq' : CS' ⥤ CG''} {Ls' : CG'' ⥤ CGp} {Lsq' : CS' ⥤ CGp} {Lp' : CT' ⥤ CG''}
  {Rp' : CG'' ⥤ CT'} {Rs' : CGp ⥤ CG''} {Lsp' : CT' ⥤ CGp} {Rsp' : CGp ⥤ CT'}
  (adjp : Lp ⊣ Rp) (adjs : Ls ⊣ Rs) (adjsp : Lsp ⊣ Rsp)
  (adjp' : Lp' ⊣ Rp') (adjs' : Ls' ⊣ Rs') (adjsp' : Lsp' ⊣ Rsp')
  {TS : CS ⥤ CS'} {TG' : CG' ⥤ CG''} {TG : CG ⥤ CGp} {TT : CT ⥤ CT'}
  (eq : Lq ⋙ TG' ≅ TS ⋙ Lq') (es : Ls ⋙ TG ≅ TG' ⋙ Ls') (esq : Lsq ⋙ TG ≅ TS ⋙ Lsq')
  (ep : Lp ⋙ TG' ≅ TT ⋙ Lp') (esp : Lsp ⋙ TG ≅ TT ⋙ Lsp')
  (cq : Lsq ≅ Lq ⋙ Ls) (cq' : Lsq' ≅ Lq' ⋙ Ls') (cp : Lsp ≅ Lp ⋙ Ls) (cp' : Lsp' ≅ Lp' ⋙ Ls')

/-- **Unit transports commute with compatible comparisons**, in abstract categories. Let
`Lp ⊣ Rp`, `Ls ⊣ Rs`, `Lsp ⊣ Rsp` be adjunctions with a composition isomorphism
`cp : Lsp ≅ Lp ⋙ Ls`, let `cq : Lsq ≅ Lq ⋙ Ls` be another composition isomorphism, and similarly
on the primed side. Let `T` be functors with isomorphisms `e : L ⋙ T ≅ T ⋙ L'` compatible with
the composition isomorphisms. Then the unit transport `Rp Lq ⟶ Rp Rs Ls Lq ≅ Rsp Lsq` commutes
with the comparisons `T Rp Lq ⟶ Rp' T Lq ≅ Rp' Lq' T` built from the mates of the `e⁻¹`. -/
lemma map_unitTransport_comp_mateEquiv_app
    (hq : ∀ M, esq.hom.app M ≫ cq'.hom.app (TS.obj M) =
      TG.map (cq.hom.app M) ≫ es.hom.app (Lq.obj M) ≫ Ls'.map (eq.hom.app M))
    (hp : ∀ M, esp.hom.app M ≫ cp'.hom.app (TT.obj M) =
      TG.map (cp.hom.app M) ≫ es.hom.app (Lp.obj M) ≫ Ls'.map (ep.hom.app M))
    (K : CS) :
    TT.map (Rp.map (adjs.unit.app (Lq.obj K)) ≫
        (conjugateIsoEquiv (adjp.comp adjs) adjsp cp).hom.app (Ls.obj (Lq.obj K)) ≫
        Rsp.map (cq.inv.app K)) ≫
        (mateEquiv adjsp adjsp' (.mk _ _ _ _ esp.inv)).app (Lsq.obj K) ≫
          Rsp'.map (esq.hom.app K) =
      ((mateEquiv adjp adjp' (.mk _ _ _ _ ep.inv)).app (Lq.obj K) ≫
        Rp'.map (eq.hom.app K)) ≫
        Rp'.map (adjs'.unit.app (Lq'.obj (TS.obj K))) ≫
        (conjugateIsoEquiv (adjp'.comp adjs') adjsp' cp').hom.app (Ls'.obj (Lq'.obj (TS.obj K))) ≫
        Rsp'.map (cq'.inv.app (TS.obj K)) := by
  have hq' : TG.map (cq.inv.app K) ≫ esq.hom.app K =
      es.hom.app (Lq.obj K) ≫ Ls'.map (eq.hom.app K) ≫ cq'.inv.app (TS.obj K) := by
    rw [← cancel_epi (TG.map (cq.hom.app K)), ← TG.map_comp_assoc, Iso.hom_inv_id_app,
      TG.map_id, Category.id_comp, ← reassoc_of% (hq K), Iso.hom_inv_id_app, Category.comp_id]
  have hβ := (mateEquiv adjsp adjsp' (.mk _ _ _ _ esp.inv)).naturality (cq.inv.app K)
  have hβp := (mateEquiv adjp adjp' (.mk _ _ _ _ ep.inv)).naturality
    (adjs.unit.app (Lq.obj K))
  have hρ := (conjugateIsoEquiv (adjp'.comp adjs') adjsp' cp').hom.naturality
    (Ls'.map (eq.hom.app K))
  have hη : eq.hom.app K ≫ adjs'.unit.app (Lq'.obj (TS.obj K)) =
      adjs'.unit.app (TG'.obj (Lq.obj K)) ≫ Rs'.map (Ls'.map (eq.hom.app K)) :=
    (adjs'.unit_naturality _).symm
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map, Functor.id_obj] at hβ hβp hρ
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hβ, ← Rsp'.map_comp, hq', reassoc_of% (mateEquiv_conjugateIsoEquiv_comp_app
    adjp adjs adjsp adjp' adjs' adjsp' ep es esp cp cp' hp (Ls.obj (Lq.obj K))),
    reassoc_of% hβp, Rsp'.map_comp, Rsp'.map_comp]
  have hρ₂ := (conjugateIsoEquiv (adjp'.comp adjs') adjsp' cp').hom.naturality
    (es.hom.app (Lq.obj K))
  dsimp only [Functor.comp_map, Functor.comp_obj] at hρ₂
  rw [← reassoc_of% hρ₂, ← reassoc_of% hρ, ← Rp'.map_comp_assoc, ← Rp'.map_comp_assoc,
    ← Rp'.map_comp_assoc, ← Rp'.map_comp_assoc, hη,
    Category.assoc (TG'.map _), map_unit_comp_mateEquiv_app_comp]

end UnitTransport

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]

/-- **The push comparisons are compatible with the composition of derived pushforwards**: for
`p : X ⟶ Y`, `q : Y ⟶ Z`, the comparison `derivedUpperStarExtendScalarsPushHom a (p ≫ q)` is the
composite of those of `q` and `p` up to the isomorphisms `Rp_* ⋙ Rq_* ≅ R(p ≫ q)_*`. -/
lemma derivedUpperStarExtendScalarsPushHom_comp_app {X Y Z : Scheme.{u}} (p : X ⟶ Y)
    (q : Y ⟶ Z)
    (N : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    L(Mod.extendScalars (coefficientMap a Z)).map
        ((rightDerivedLowerStarComp Λ p q).hom.app N) ≫
        (derivedUpperStarExtendScalarsPushHom a (p ≫ q)).app N =
      (derivedUpperStarExtendScalarsPushHom a q).app (R((p)_*⟦Λ⟧).obj N) ≫
        R((q)_*⟦Λ'⟧).map ((derivedUpperStarExtendScalarsPushHom a p).app N) ≫
        (rightDerivedLowerStarComp Λ' p q).hom.app
          (L(Mod.extendScalars (coefficientMap a X)).obj N) :=
  mateEquiv_conjugateIsoEquiv_comp_app (derivedUpperStarLowerStarAdjunction Λ q)
    (derivedUpperStarLowerStarAdjunction Λ p) (derivedUpperStarLowerStarAdjunction Λ (p ≫ q))
    (derivedUpperStarLowerStarAdjunction Λ' q) (derivedUpperStarLowerStarAdjunction Λ' p)
    (derivedUpperStarLowerStarAdjunction Λ' (p ≫ q)) (derivedUpperStarExtendScalarsIso a q)
    (derivedUpperStarExtendScalarsIso a p) (derivedUpperStarExtendScalarsIso a (p ≫ q))
    (leftDerivedUpperStarComp Λ p q) (leftDerivedUpperStarComp Λ' p q)
    (derivedUpperStarExtendScalarsIsoCompCoherence a p q) N

/-- The comparison `T (Rp_* Lq^* K) ⟶ Rp_* T (Lq^* K) ≅ Rp_* Lq^* (T K)` between the derived
extension of scalars `T` along `a` and `Rp_* Lq^*`: the push comparison
`derivedUpperStarExtendScalarsPushHom a p` followed by the pull isomorphism
`derivedUpperStarExtendScalarsIso a q`. -/
noncomputable def derivedPushPullExtendScalarsHom {G T S : Scheme.{u}} (p : G ⟶ T) (q : G ⟶ S)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))) :
    L(Mod.extendScalars (coefficientMap a T)).obj (R((p)_*⟦Λ⟧).obj (L((q)^*⟦Λ⟧).obj K)) ⟶
      R((p)_*⟦Λ'⟧).obj (L((q)^*⟦Λ'⟧).obj (L(Mod.extendScalars (coefficientMap a S)).obj K)) :=
  (derivedUpperStarExtendScalarsPushHom a p).app (L((q)^*⟦Λ⟧).obj K) ≫
    R((p)_*⟦Λ'⟧).map ((derivedUpperStarExtendScalarsIso a q).hom.app K)

/-- **Extension of scalars carries the derived unit to the derived unit**: `T` of the unit
`K ⟶ Rq_* Lq^* K` followed by the comparison `derivedPushPullExtendScalarsHom a q q K` is the unit
`T K ⟶ Rq_* Lq^* (T K)` with coefficients `Λ'`. -/
theorem map_unit_comp_derivedPushPullExtendScalarsHom {X Y : Scheme.{u}} (q : Y ⟶ X)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    L(Mod.extendScalars (coefficientMap a X)).map
        ((derivedUpperStarLowerStarAdjunction Λ q).unit.app K) ≫
        derivedPushPullExtendScalarsHom a q q K =
      (derivedUpperStarLowerStarAdjunction Λ' q).unit.app
        (L(Mod.extendScalars (coefficientMap a X)).obj K) :=
  map_unit_comp_mateEquiv_app_comp (derivedUpperStarLowerStarAdjunction Λ q)
    (derivedUpperStarLowerStarAdjunction Λ' q) (derivedUpperStarExtendScalarsIso a q) K

-- the composites of derived functors with coefficients `Λ'` are slow to unify
/-- **Extension of scalars commutes with the derived unit transport**: for `s : G ⟶ G'` with
`s ≫ p = p₁` and `s ≫ q = q₁`, the comparisons `derivedPushPullExtendScalarsHom` intertwine `T`
of the unit transport `Rp_* Lq^* K ⟶ R(p₁)_* L(q₁)^* K` with coefficients `Λ` and the unit
transport at `T K` with coefficients `Λ'`. -/
theorem map_derivedUnitTransport_comp_derivedPushPullExtendScalarsHom {G G' T S : Scheme.{u}}
    (s : G ⟶ G') {p : G' ⟶ T} {q : G' ⟶ S} {p₁ : G ⟶ T} {q₁ : G ⟶ S} (hp : s ≫ p = p₁)
    (hq : s ≫ q = q₁)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))) :
    L(Mod.extendScalars (coefficientMap a T)).map (derivedUnitTransport Λ s hp hq K) ≫
        derivedPushPullExtendScalarsHom a p₁ q₁ K =
      derivedPushPullExtendScalarsHom a p q K ≫
        derivedUnitTransport Λ' s hp hq (L(Mod.extendScalars (coefficientMap a S)).obj K) := by
  subst hp hq
  refine Eq.trans ?_ (congrArg (derivedPushPullExtendScalarsHom a p q K ≫ ·)
    (derivedUnitTransport_rfl Λ' s p q (L(Mod.extendScalars (coefficientMap a S)).obj K)).symm)
  rw [derivedUnitTransport_rfl Λ s p q K]
  unfold derivedPushPullExtendScalarsHom
  exact map_unitTransport_comp_mateEquiv_app (derivedUpperStarLowerStarAdjunction Λ p)
    (derivedUpperStarLowerStarAdjunction Λ s) (derivedUpperStarLowerStarAdjunction Λ (s ≫ p))
    (derivedUpperStarLowerStarAdjunction Λ' p) (derivedUpperStarLowerStarAdjunction Λ' s)
    (derivedUpperStarLowerStarAdjunction Λ' (s ≫ p)) (derivedUpperStarExtendScalarsIso a q)
    (derivedUpperStarExtendScalarsIso a s) (derivedUpperStarExtendScalarsIso a (s ≫ q))
    (derivedUpperStarExtendScalarsIso a p) (derivedUpperStarExtendScalarsIso a (s ≫ p))
    (leftDerivedUpperStarComp Λ s q) (leftDerivedUpperStarComp Λ' s q)
    (leftDerivedUpperStarComp Λ s p) (leftDerivedUpperStarComp Λ' s p)
    (derivedUpperStarExtendScalarsIsoCompCoherence a s q)
    (derivedUpperStarExtendScalarsIsoCompCoherence a s p) K

/-- The comparison `derivedPushPullExtendScalarsHom a p q K` is an isomorphism as soon as the
push comparison `derivedUpperStarExtendScalarsPushHom a p` is invertible at `Lq^* K`. -/
instance isIso_derivedPushPullExtendScalarsHom {G T S : Scheme.{u}} (p : G ⟶ T) (q : G ⟶ S)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)))
    [IsIso ((derivedUpperStarExtendScalarsPushHom a p).app (L((q)^*⟦Λ⟧).obj K))] :
    IsIso (derivedPushPullExtendScalarsHom a p q K) := by
  unfold derivedPushPullExtendScalarsHom
  infer_instance

/-- If the push comparison `derivedUpperStarExtendScalarsPushHom a q` is invertible at `Lq^* K`,
then `T` of the unit `K ⟶ Rq_* Lq^* K` and the unit `T K ⟶ Rq_* Lq^* (T K)` with coefficients
`Λ'` are isomorphic arrows. -/
noncomputable def arrowIsoMapUnit {X Y : Scheme.{u}} (q : Y ⟶ X)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    [IsIso ((derivedUpperStarExtendScalarsPushHom a q).app (L((q)^*⟦Λ⟧).obj K))] :
    Arrow.mk (L(Mod.extendScalars (coefficientMap a X)).map
        ((derivedUpperStarLowerStarAdjunction Λ q).unit.app K)) ≅
      Arrow.mk ((derivedUpperStarLowerStarAdjunction Λ' q).unit.app
        (L(Mod.extendScalars (coefficientMap a X)).obj K)) :=
  Arrow.isoMk (Iso.refl _) (asIso (derivedPushPullExtendScalarsHom a q q K)) (by
    simp [map_unit_comp_derivedPushPullExtendScalarsHom])

/-- If the push comparison `derivedUpperStarExtendScalarsPushHom a g` is invertible at `Lg^* K`,
then for `s : G ⟶ G` with `s ≫ g = g`, `T` of the unit transport along `s` of `Rg_* Lg^* K` and
the unit transport along `s` of `Rg_* Lg^* (T K)` with coefficients `Λ'` are isomorphic arrows.
-/
noncomputable def arrowIsoMapDerivedUnitTransport {G X : Scheme.{u}} (s : G ⟶ G)
    {g : G ⟶ X} (hs : s ≫ g = g)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    [IsIso ((derivedUpperStarExtendScalarsPushHom a g).app (L((g)^*⟦Λ⟧).obj K))] :
    Arrow.mk (L(Mod.extendScalars (coefficientMap a X)).map
        (derivedUnitTransport Λ s hs hs K)) ≅
      Arrow.mk (derivedUnitTransport Λ' s hs hs
        (L(Mod.extendScalars (coefficientMap a X)).obj K)) :=
  Arrow.isoMk (asIso (derivedPushPullExtendScalarsHom a g g K))
    (asIso (derivedPushPullExtendScalarsHom a g g K))
    (map_derivedUnitTransport_comp_derivedPushPullExtendScalarsHom a s hs hs K).symm

end AlgebraicGeometry.ProEtale.CondensedRing
