/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.CompactSupportExchange
public import WeilConjectures.TraceFormula.Specialization.CompactificationRouteCoherence
public import WeilConjectures.TraceFormula.Specialization.ComponentUnitClassF

/-!

# The exchange of the fixed loci on `j_! ℚ̄_ℓ`, from the fixed-square exchange

Let `j : B ⟶ F` be a proper open subscheme of the fixed locus `F ⟶[d] X`, with special analogue
`r : B'' ⟶ F'` and `d' : F' ⟶ X'`. The identity
`ν_F(j_! ℚ̄_ℓ) ≫ Ψ_s(Ra_{F!} j_! ≅ Ra_{X!} d_! j_! ⟶ Ra_{X!} R(dj)_* ≅ Ra_{B!}) = …`
given by the fixed-square exchange and the normal form of `ν_X` determines `ν_F(j_! ℚ̄_ℓ)`, once
the composition isomorphisms of the lower shriek are identified on both fibres:

* `Ra_{B!} ≅ Ra_{F!} j_! ≅ Ra_{X!} d_! j_! ≅ Ra_{X!} R(dj)_! ≅ Ra_{B!}` is the identity
  (`ProEtale.CondensedRing.lowerShriekCompOfEq_hom_app_comp_hom_app_comp_map_inv_comp_inv`);
* `Ra_{X'!} d'_! r_! ≅ Ra_{X'!} R(d'r)_! ≅ Ra_{X'!} R(d'r)_* = Ra_{X'!} Rg''_* ≅ Ra_{X'!} Rg''_!
  ≅ Ra_{B''!}` is `Ra_{F'!} r_! ≅ Ra_{B''!}`
  (`ProEtale.CondensedRing.lowerShriekCompOfEq_hom_app_comp_map_comp_inv_eq`).

The algebra is `CategoryTheory.exchange_app_eq_of_fixedSquare_aux`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

variable {CB CF CX CP CC CB' CF' CX' CP' CC' : Type*} [Category CB] [Category CF] [Category CX]
  [Category CP] [Category CC] [Category CB'] [Category CF'] [Category CX'] [Category CP']
  [Category CC']

/-- **The exchange of the fixed loci on `j_! 𝟙`**, abstractly: from the identity `h` (the
fixed-square exchange followed by the normal form of `ν_X`), the composition isomorphism
coherences `hS3` (generic fibre) and `hS4` (special fibre) and `a₂ = c₂`, the exchange `νFN` is
`a_{F'}(y ≫ r_!≅r_*⁻¹) ≫ e_{F'}⁻¹ ≫ ν_B ≫ Ψ(e_F)`, i.e. the square
```
aF'(ι'U (ΨC (ιL (Jsh K)))) ---------- νFN ---------> Ψ(aF(Jsh K))
            |                                              ^
  aF'(y ≫ isoR⁻¹)                                      Ψ(eF)
            v                                              |
      aF'(Rsh Q) ----- eF'⁻¹ -----> aB' Q ----- νB -----> Ψ(aB K)
```
commutes, where `y = ι'U(ΨC(ιL(isoJ) ≫ c₂) ≫ z) ≫ ε`. -/
theorem exchange_app_eq_of_fixedSquare_aux (Ψ : CP ⥤ CP')
    {aB : CB ⥤ CP} {aF : CF ⥤ CP} {aX : CX ⥤ CP}
    {aB' : CB' ⥤ CP'} {aF' : CF' ⥤ CP'} {aX' : CX' ⥤ CP'}
    {Jsh Jst : CB ⥤ CF} (isoJ : Jsh ≅ Jst) {Dsh : CF ⥤ CX} {Gsh Gst : CB ⥤ CX}
    (isoG : Gsh ≅ Gst) (cJD : Gsh ≅ Jsh ⋙ Dsh) (eF : aB ≅ Jsh ⋙ aF) (eX : aF ≅ Dsh ⋙ aX)
    (eG : aB ≅ Gsh ⋙ aX) (K : CB)
    {Rsh Rst : CB' ⥤ CF'} (isoR : Rsh ≅ Rst) {D'sh : CF' ⥤ CX'} {RDsh RDst : CB' ⥤ CX'}
    (isoRD : RDsh ≅ RDst) {G''sh G''st : CB' ⥤ CX'} (isoG'' : G''sh ≅ G''st)
    (cRD : RDsh ≅ Rsh ⋙ D'sh) (eF' : aB' ≅ Rsh ⋙ aF') (eX' : aF' ≅ D'sh ⋙ aX')
    (eG'' : aB' ≅ G''sh ⋙ aX') (Q : CB') (tr : RDst.obj Q ⟶ G''st.obj Q)
    {ιL : CF ⥤ CC} {ΨC : CC ⥤ CC'} {ι'L : CF' ⥤ CC'} {ι'U : CC' ⥤ CF'}
    (ε : ι'U.obj (ι'L.obj (Rst.obj Q)) ⟶ Rst.obj Q) {Y : CC}
    (a₂ c₂ : ιL.obj (Jst.obj K) ⟶ Y) (z : ΨC.obj Y ⟶ ι'L.obj (Rst.obj Q))
    (νFN : aF'.obj (ι'U.obj (ΨC.obj (ιL.obj (Jsh.obj K)))) ⟶ Ψ.obj (aF.obj (Jsh.obj K)))
    (νB : aB'.obj Q ⟶ Ψ.obj (aB.obj K))
    (h : νFN ≫ Ψ.map (eX.hom.app (Jsh.obj K) ≫ aX.map (Dsh.map (isoJ.hom.app K) ≫
        Dsh.map (isoJ.inv.app K) ≫ cJD.inv.app K ≫ isoG.hom.app K)) ≫
        Ψ.map (aX.map (isoG.inv.app K) ≫ eG.inv.app K) =
      eX'.hom.app (ι'U.obj (ΨC.obj (ιL.obj (Jsh.obj K)))) ≫
        aX'.map (D'sh.map (ι'U.map (ΨC.map (ιL.map (isoJ.hom.app K) ≫ a₂) ≫ z) ≫ ε) ≫
          ((D'sh.map (isoR.inv.app Q) ≫ cRD.inv.app Q ≫ isoRD.hom.app Q) ≫ tr)) ≫
        aX'.map (isoG''.inv.app Q) ≫ eG''.inv.app Q ≫ νB)
    (hS3 : eF.hom.app K ≫ eX.hom.app (Jsh.obj K) ≫ aX.map (cJD.inv.app K) ≫ eG.inv.app K = 𝟙 _)
    (hS4 : eX'.hom.app (Rsh.obj Q) ≫ aX'.map (cRD.inv.app Q ≫ isoRD.hom.app Q ≫ tr ≫
        isoG''.inv.app Q) ≫ eG''.inv.app Q = eF'.inv.app Q)
    (hac : a₂ = c₂) :
    νFN = (aF'.map ((ι'U.map (ΨC.map (ιL.map (isoJ.hom.app K) ≫ c₂) ≫ z) ≫ ε) ≫
        isoR.inv.app Q) ≫ eF'.inv.app Q) ≫ νB ≫ Ψ.map (eF.hom.app K) := by
  subst hac
  have hS3' : eX.hom.app (Jsh.obj K) ≫ aX.map (cJD.inv.app K) ≫ eG.inv.app K = eF.inv.app K := by
    rw [← cancel_epi (eF.hom.app K), hS3, Iso.hom_inv_id_app]
  have hL : Ψ.map (eX.hom.app (Jsh.obj K) ≫ aX.map (Dsh.map (isoJ.hom.app K) ≫
        Dsh.map (isoJ.inv.app K) ≫ cJD.inv.app K ≫ isoG.hom.app K)) ≫
        Ψ.map (aX.map (isoG.inv.app K) ≫ eG.inv.app K) = Ψ.map (eF.inv.app K) := by
    rw [← Ψ.map_comp, ← hS3']
    congr 1
    simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app, Functor.map_comp, Category.assoc,
      CategoryTheory.Functor.map_id, Category.id_comp]
  have hn := eX'.hom.naturality ((ι'U.map (ΨC.map (ιL.map (isoJ.hom.app K) ≫ a₂) ≫ z) ≫ ε) ≫
    isoR.inv.app Q)
  simp only [Functor.comp_map] at hn
  rw [hL] at h
  rw [← cancel_mono (Ψ.map (eF.inv.app K)), h]
  simp only [Category.assoc, ← Ψ.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.comp_id]
  rw [← hS4]
  simp only [Functor.map_comp, Category.assoc] at hn ⊢
  rw [reassoc_of% hn]

/-- Gluing an identity `c ≫ L(s ≫ q) ≫ r = w ≫ v` to `w ≫ v ≫ ν = Z`: the composite
`c ≫ L(s) ≫ (L(q) ≫ r) ≫ ν` is `Z`. -/
lemma comp_map_comp_comp_eq_of_eq' {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] {L : 𝒞 ⥤ 𝒟}
    {u A₁ A₂ B₀ : 𝒟} {U₁ U₂ U₃ : 𝒞} (c : u ⟶ L.obj U₁) (s : U₁ ⟶ U₂) (q : U₂ ⟶ U₃)
    (r : L.obj U₃ ⟶ A₁) (w : u ⟶ A₂) (v : A₂ ⟶ A₁) (ν : A₁ ⟶ B₀) (Z : u ⟶ B₀)
    (h : c ≫ L.map (s ≫ q) ≫ r = w ≫ v) (h' : w ≫ v ≫ ν = Z) :
    c ≫ L.map s ≫ (L.map q ≫ r) ≫ ν = Z := by
  rw [← h', ← reassoc_of% h, L.map_comp]; simp only [Category.assoc]

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {B F X P : Over (Spec (.of k))} [LocallyOfFiniteType B.hom] [QuasiCompact B.hom]
  [IsSeparated B.hom] [LocallyOfFiniteType F.hom] [QuasiCompact F.hom] [IsSeparated F.hom]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]

/-- `Ra_! ≅ Ra_{F!} j_! ≅ Ra_{X!} d_! j_! ≅ Ra_{X!} R(dj)_! ≅ Ra_!` is the identity. -/
theorem lowerShriekCompOfEq_hom_app_comp_hom_app_comp_map_inv_comp_inv (j : B ⟶ F) (d : F ⟶ X)
    {a : B ⟶ P} {aF : F ⟶ P} (aX : X ⟶ P) (wF : j ≫ aF = a) (wX : d ≫ aX = aF)
    (wB : (j ≫ d) ≫ aX = a) (K : Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (lowerShriekCompOfEq ℓ j aF wF).hom.app K ≫
      (lowerShriekCompOfEq ℓ d aX wX).hom.app ((boundedConstructibleLowerShriek ℓ j).obj K) ≫
      (boundedConstructibleLowerShriek ℓ aX).map
        ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ j d).inv.app K) ≫
      (lowerShriekCompOfEq ℓ (j ≫ d) aX wB).inv.app K = 𝟙 _ := by
  subst wF wX
  have h := lowerShriekComp_hom_app_comp_map_inv_comp_inv ℓ j d aX K
  simp only [lowerShriekCompOfEq, Iso.trans_hom, Iso.trans_inv, NatTrans.comp_app, eqToIso.hom,
    eqToIso.inv, eqToHom_refl, Category.id_comp]
  rw [reassoc_of% h]
  simp

/-- `Ra_{X!} d_! r_! ≅ Ra_{X!} R(rd)_! ≅ Ra_{X!} R(rd)_* = Ra_{X!} Rg_* ≅ Ra_{X!} Rg_! ≅ Ra_!` is
`Ra_{F!} r_! ≅ Ra_!`, for `r ≫ d = g` proper. -/
theorem lowerShriekCompOfEq_hom_app_comp_map_comp_inv_eq (r : B ⟶ F) (d : F ⟶ X) {g : B ⟶ X}
    (hg : r ≫ d = g) [IsProper (r ≫ d).left] [IsProper g.left] {a : B ⟶ P} {aF : F ⟶ P}
    (aX : X ⟶ P) (wF : r ≫ aF = a) (wX : d ≫ aX = aF) (wG : g ≫ aX = a)
    (Q : Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hQ : (boundedConstructibleLowerStar ℓ (r ≫ d)).obj Q =
      (boundedConstructibleLowerStar ℓ g).obj Q) :
    (lowerShriekCompOfEq ℓ d aX wX).hom.app ((boundedConstructibleLowerShriek ℓ r).obj Q) ≫
      (boundedConstructibleLowerShriek ℓ aX).map
        ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ r d).inv.app Q ≫
          (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (r ≫ d)).hom.app Q ≫
          eqToHom hQ ≫ (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).inv.app Q) ≫
      (lowerShriekCompOfEq ℓ g aX wG).inv.app Q = (lowerShriekCompOfEq ℓ r aF wF).inv.app Q := by
  subst hg
  rw [eqToHom_refl, Category.id_comp, Iso.hom_inv_id_app, Category.comp_id,
    ← cancel_epi ((lowerShriekCompOfEq ℓ r aF wF).hom.app Q), Iso.hom_inv_id_app]
  exact lowerShriekCompOfEq_hom_app_comp_hom_app_comp_map_inv_comp_inv ℓ r d aX wF wX wG Q

omit [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom] in
/-- `Rj_* ⋙ Rι_* ≅ R(jι)_*` along `rfl` is the composition isomorphism. -/
lemma boundedConstructibleLowerStarCompOfEq_hom_app_rfl (j : B ⟶ F) (ι : F ⟶ X)
    (K : Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerStarCompOfEq ℓ j ι rfl).hom.app K =
      (boundedConstructibleLowerStarComp ℓ j ι).hom.app K := by
  simp [boundedConstructibleLowerStarCompOfEq]

end AlgebraicGeometry.ProEtale.CondensedRing
