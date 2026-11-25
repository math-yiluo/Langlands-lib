/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SecSmoothPurity.CochainCoefficientArrows
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators

/-! # Associativity and symmetry of the ordinary module comparison

Source: Stacks Project, sites-modules.tex, Tag 03EL, and
sites-cohomology.tex, Tag 07A4.
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe w uC vC uD vD uE vE
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace CategoryTheory.CochainPullback
set_option autoImplicit false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] SheafOfModules.monoidalCategory

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {R : Sheaf J CommRingCat.{w}} {S : Sheaf K CommRingCat.{w}}

private noncomputable def swappedComparison (f : RingedPullback R S) (k : Comparison f) :
    Comparison f where
  q := k.q
  q_one := k.q_one
  mu M N := f.L.mapIso (β_ M N) ≪≫ k.mu N M ≪≫ β_ (f.L.obj N) (f.L.obj M)
  naturality := by
    intro M M' N N' a b
    simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
    rw [← f.L.map_comp_assoc, BraidedCategory.braiding_naturality, f.L.map_comp]
    simp only [Category.assoc]
    rw [← Category.assoc (f.L.map (b ⊗ₘ a)) (k.mu N' M').hom,
      k.naturality]
    simp only [Category.assoc]
    rw [← BraidedCategory.braiding_naturality]
  pure := by
    intro M N Z x y z hz W t
    let z' := z ≫ (underlying R).map (β_ M N).hom
    have hz' : ∀ (U : Cᵒᵖ) (s : Z.obj.obj U),
        z'.hom.app U s = moduleTmul N M U (y.hom.app U s) (x.hom.app U s) := by
      intro U s
      change (β_ M N).hom.val.app U (z.hom.app U s) = _
      rw [hz]
      exact moduleTmul_braiding M N U _ _
    have hp := k.pure N M Z y x z' hz' W t
    have hn : f.uInv.map z' ≫ f.I.moduleUnderlying.inv.app (N ⊗ M) ≫ k.q (N ⊗ M) =
        f.uInv.map z ≫ f.I.moduleUnderlying.inv.app (M ⊗ N) ≫ k.q (M ⊗ N) ≫
          (underlying S).map (f.L.map (β_ M N).hom) := by
      dsimp only [z']
      simp only [Functor.map_comp, Category.assoc]
      have hi := f.I.moduleUnderlying.inv.naturality (β_ M N).hom
      change f.uInv.map ((underlying R).map (β_ M N).hom) ≫
          f.I.moduleUnderlying.inv.app (N ⊗ M) =
        f.I.moduleUnderlying.inv.app (M ⊗ N) ≫
          (underlying f.RI).map (f.I.modules.map (β_ M N).hom) at hi
      rw [← Category.assoc (f.uInv.map ((underlying R).map (β_ M N).hom))
        (f.I.moduleUnderlying.inv.app (N ⊗ M)), hi]
      simp only [Category.assoc]
      rw [comparison_q_naturality]
    change _ = moduleTmul (f.L.obj N) (f.L.obj M) W
      ((generator f k y).hom.app W t) ((generator f k x).hom.app W t) at hp
    have hp' := congrArg
      (fun s ↦ (β_ (f.L.obj N) (f.L.obj M)).hom.val.app W s) hp
    rw [moduleTmul_braiding] at hp'
    have hp'' : ((generator f k z' ≫ (underlying S).map (k.mu N M).hom ≫
        (underlying S).map (β_ (f.L.obj N) (f.L.obj M)).hom).hom.app W) t =
        moduleTmul (f.L.obj M) (f.L.obj N) W
          ((generator f k x).hom.app W t) ((generator f k y).hom.app W t) := hp'
    have he := congrArg (fun s ↦
      ((s ≫ (underlying S).map (k.mu N M).hom ≫
        (underlying S).map (β_ (f.L.obj N) (f.L.obj M)).hom).hom.app W) t) hn
    change _ = moduleTmul (f.L.obj M) (f.L.obj N) W
      ((generator f k x).hom.app W t) ((generator f k y).hom.app W t)
    have hh := he.symm.trans hp''
    simpa only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp,
      Category.assoc] using hh

/-- The normalized module tensor comparison preserves the symmetry.
Source: Stacks 03EL and 03EK (auxiliary; not a blueprint node).
Proof: swapping the source and target factors gives a comparison with the same pure
formula, by the sheafification braiding formula. Uniqueness identifies it with k. -/
theorem cochainModuleTensorBraiding (f : RingedPullback R S) (k : Comparison f)
    (M N : Modules R) :
    f.L.map (β_ M N).hom ≫ (k.mu N M).hom =
      (k.mu M N).hom ≫ (β_ (f.L.obj M) (f.L.obj N)).hom := by
  let := f.finiteLimits
  let := (SheafOfModules.CochainTensorComparison.canonicalRingedTensorComparison_existsUnique
    R S f.RI f.uInv f.I f.coefficient f.L f.hobj f.uPush f.adj f.hmap).2
  have he : swappedComparison f k = k := Subsingleton.elim _ _
  have hm := congrArg (fun k : Comparison f ↦ (k.mu M N).hom) he
  apply (cancel_mono (β_ (f.L.obj N) (f.L.obj M)).hom).1
  simpa only [swappedComparison, Iso.trans_hom, Functor.mapIso_hom,
    Category.assoc, SymmetricCategory.symmetry, Category.comp_id] using hm

private theorem productElements {A : Type uE} [Category.{vE} A] [HasBinaryProducts A]
    (F : A ⥤ Type w) (X Y : A) [PreservesLimit (pair X Y) F]
    (x : F.obj X) (y : F.obj Y) :
    ∃ t : F.obj (X ⨯ Y), F.map prod.fst t = x ∧ F.map prod.snd t = y := by
  let e := asIso (prodComparison F X Y) ≪≫ Types.binaryProductIso (F.obj X) (F.obj Y)
  have hf : e.hom ≫ ↾_root_.Prod.fst = F.map prod.fst := by
    dsimp only [e, Iso.trans_hom, asIso_hom]
    rw [Category.assoc, Types.binaryProductIso_hom_comp_fst, prodComparison_fst]
  have hs : e.hom ≫ ↾_root_.Prod.snd = F.map prod.snd := by
    dsimp only [e, Iso.trans_hom, asIso_hom]
    rw [Category.assoc, Types.binaryProductIso_hom_comp_snd, prodComparison_snd]
  refine ⟨e.inv (x, y), ?_, ?_⟩
  · rw [← hf]
    change (e.hom (e.inv (x, y))).1 = x
    rw [Iso.inv_hom_id_apply]
  · rw [← hs]
    change (e.hom (e.inv (x, y))).2 = y
    rw [Iso.inv_hom_id_apply]

-- Tensoring the three transported scalar extensions needs dependent conversions.
private theorem triple_hom_ext (f : RingedPullback R S) (k : Comparison f)
    (M N P : Modules R) (H : Modules S)
    {a b : (f.L.obj M ⊗ f.L.obj N) ⊗ f.L.obj P ⟶ H}
    (h : ∀ (W : Dᵒᵖ) (m : (f.I.modules.obj M).val.obj W)
      (n : (f.I.modules.obj N).val.obj W) (p : (f.I.modules.obj P).val.obj W),
      a.val.app W (moduleTmul _ _ W
        (moduleTmul _ _ W ((k.q M).hom.app W m) ((k.q N).hom.app W n))
        ((k.q P).hom.app W p)) =
      b.val.app W (moduleTmul _ _ W
        (moduleTmul _ _ W ((k.q M).hom.app W m) ((k.q N).hom.app W n))
        ((k.q P).hom.app W p))) : a = b := by
  let eM := eqToIso (f.hobj M).symm
  let eN := eqToIso (f.hobj N).symm
  let eP := eqToIso (f.hobj P).symm
  apply (cancel_epi ((eM.hom ⊗ₘ eN.hom) ⊗ₘ eP.hom)).mp
  apply scalarTensor_hom_ext₃ f.coefficient
    (f.I.modules.obj M) (f.I.modules.obj N) (f.I.modules.obj P) H
  intro W m n p
  change a.val.app W (((eM.hom ⊗ₘ eN.hom) ⊗ₘ eP.hom).val.app W _) =
    b.val.app W (((eM.hom ⊗ₘ eN.hom) ⊗ₘ eP.hom).val.app W _)
  rw [moduleTmul_map, moduleTmul_map]
  have hM : eM.hom.val.app W
      (extensionTmul f.coefficient (f.I.modules.obj M) W 1 m) =
        (k.q M).hom.app W m := (k.q_one M W m).symm
  have hN : eN.hom.val.app W
      (extensionTmul f.coefficient (f.I.modules.obj N) W 1 n) =
        (k.q N).hom.app W n := (k.q_one N W n).symm
  have hP : eP.hom.val.app W
      (extensionTmul f.coefficient (f.I.modules.obj P) W 1 p) =
        (k.q P).hom.app W p := (k.q_one P W p).symm
  rw [hM, hN, hP]
  exact h W m n p

private theorem generator_triple_elements (f : RingedPullback R S) (k : Comparison f)
    (M N P : Modules R) (W : Dᵒᵖ) (m : (f.I.modules.obj M).val.obj W)
    (n : (f.I.modules.obj N).val.obj W) (p : (f.I.modules.obj P).val.obj W) :
    ∃ (Z : Sheaf J (Type w)) (x : Z ⟶ (underlying R).obj M)
      (y : Z ⟶ (underlying R).obj N) (z : Z ⟶ (underlying R).obj P)
      (t : (f.uInv.obj Z).obj.obj W),
      (generator f k x).hom.app W t = (k.q M).hom.app W m ∧
      (generator f k y).hom.app W t = (k.q N).hom.app W n ∧
      (generator f k z).hom.app W t = (k.q P).hom.app W p := by
  let := f.finiteLimits
  let F := f.uInv ⋙ sheafToPresheaf K (Type w) ⋙ (evaluation Dᵒᵖ (Type w)).obj W
  let X := (underlying R).obj M
  let Y := (underlying R).obj N
  let Z := (underlying R).obj P
  let m' := (f.I.moduleUnderlying.hom.app M).hom.app W m
  let n' := (f.I.moduleUnderlying.hom.app N).hom.app W n
  let p' := (f.I.moduleUnderlying.hom.app P).hom.app W p
  obtain ⟨s, hs₁, hs₂⟩ := productElements F Y Z n' p'
  obtain ⟨t, ht₁, ht₂⟩ := productElements F X (Y ⨯ Z) m' s
  refine ⟨X ⨯ (Y ⨯ Z), prod.fst, prod.snd ≫ prod.fst,
    prod.snd ≫ prod.snd, t, ?_, ?_, ?_⟩
  · change (k.q M).hom.app W ((f.I.moduleUnderlying.inv.app M).hom.app W
      ((F.map prod.fst) t)) = _
    rw [ht₁]
    have hi := congrArg (fun v ↦ v.hom.app W m) (f.I.moduleUnderlying.hom_inv_id_app M)
    exact congrArg ((k.q M).hom.app W) hi
  · change (k.q N).hom.app W ((f.I.moduleUnderlying.inv.app N).hom.app W
      ((F.map (prod.snd ≫ prod.fst)) t)) = _
    rw [F.map_comp]
    change (k.q N).hom.app W ((f.I.moduleUnderlying.inv.app N).hom.app W
      (F.map prod.fst (F.map prod.snd t))) = _
    rw [ht₂, hs₁]
    have hi := congrArg (fun v ↦ v.hom.app W n) (f.I.moduleUnderlying.hom_inv_id_app N)
    exact congrArg ((k.q N).hom.app W) hi
  · change (k.q P).hom.app W ((f.I.moduleUnderlying.inv.app P).hom.app W
      ((F.map (prod.snd ≫ prod.snd)) t)) = _
    rw [F.map_comp]
    change (k.q P).hom.app W ((f.I.moduleUnderlying.inv.app P).hom.app W
      (F.map prod.snd (F.map prod.snd t))) = _
    rw [ht₂, hs₂]
    have hi := congrArg (fun v ↦ v.hom.app W p) (f.I.moduleUnderlying.hom_inv_id_app P)
    exact congrArg ((k.q P).hom.app W) hi

-- Triple generators require dependent conversions through scalar extension.
/-- The ordinary normalized module tensor comparison respects associativity and symmetry.
Source: Stacks 03EL, lemma-tensor-product-pullback, with the tensor structure of 03EK.
(auxiliary; not a blueprint node).

Proof: evaluate associativity on generalized pure triple tensors, after inverse image
and insertion of scalar units. Both routes take s tensor ((x tensor y) tensor z) to
(s tensor x) tensor ((1 tensor y) tensor (1 tensor z)). Evaluate symmetry on generalized
pure pairs; both routes take s tensor (x tensor y) to (1 tensor y) tensor (s tensor x).
These formulas follow from the pure field of each comparison, naturality of the
inverse-image underlying-module identification, and the sheaf tensor associator and
symmetry. The scalar-extension balancing relations move s to either tensor factor.
The inverse-image functor preserves finite products, so pairs and triples of sections
are represented by generalized elements of the corresponding products. Scalar-extension
linearity and the sheafification adjunction extend equality from inserted pure tensors
to all module morphisms. No points, flatness, unit isomorphism or complexes are used.
Zero rings and zero modules satisfy the same formulas. -/
theorem cochainModuleTensorAssociativity (f : RingedPullback R S) (k : Comparison f) :
    ∀ M N H : Modules R,
      (k.mu (M ⊗ N) H).hom ≫ ((k.mu M N).hom ⊗ₘ 𝟙 _) ≫
        (α_ (f.L.obj M) (f.L.obj N) (f.L.obj H)).hom =
      f.L.map (α_ M N H).hom ≫ (k.mu M (N ⊗ H)).hom ≫
        (𝟙 _ ⊗ₘ (k.mu N H).hom) := by
  intro M N H
  let e := ((k.mu M N).symm ⊗ᵢ Iso.refl (f.L.obj H)) ≪≫ (k.mu (M ⊗ N) H).symm
  apply (cancel_epi e.hom).mp
  have he : e.hom ≫ (k.mu (M ⊗ N) H).hom ≫ ((k.mu M N).hom ⊗ₘ 𝟙 _) = 𝟙 _ := by
    exact ((k.mu (M ⊗ N) H) ≪≫ (k.mu M N ⊗ᵢ Iso.refl (f.L.obj H))).inv_hom_id
  change (e.hom ≫ (k.mu (M ⊗ N) H).hom ≫ ((k.mu M N).hom ⊗ₘ 𝟙 _)) ≫
      (α_ (f.L.obj M) (f.L.obj N) (f.L.obj H)).hom = _
  rw [he, Category.id_comp]
  apply triple_hom_ext f k M N H _
  intro W m n p
  obtain ⟨Z, x, y, z, t, hx, hy, hz⟩ := generator_triple_elements f k M N H W m n p
  let xy := moduleTensorPair x y
  let yz := moduleTensorPair y z
  let l := moduleTensorPair xy z
  let r := moduleTensorPair x yz
  have hpMN := congrArg (fun v ↦ v.hom.app W t) (generator_tensorPair f k x y)
  have hpL := congrArg (fun v ↦ v.hom.app W t) (generator_tensorPair f k xy z)
  have hpR := congrArg (fun v ↦ v.hom.app W t) (generator_tensorPair f k x yz)
  have hpNH := congrArg (fun v ↦ v.hom.app W t) (generator_tensorPair f k y z)
  have hi {A B : Modules S} (i : A ≅ B) (s : A.val.obj W) :
      i.inv.val.app W (i.hom.val.app W s) = s :=
    congrArg (fun v ↦ v.val.app W s) i.hom_inv_id
  have hli : e.hom.val.app W (moduleTmul _ _ W
      (moduleTmul _ _ W ((k.q M).hom.app W m) ((k.q N).hom.app W n))
        ((k.q H).hom.app W p)) = (generator f k l).hom.app W t := by
    rw [← hx, ← hy, ← hz]
    change (k.mu (M ⊗ N) H).inv.val.app W
      (((k.mu M N).inv ⊗ₘ 𝟙 (f.L.obj H)).val.app W
        (moduleTmul _ _ W
          (moduleTmul _ _ W ((generator f k x).hom.app W t)
            ((generator f k y).hom.app W t)) ((generator f k z).hom.app W t))) = _
    rw [moduleTmul_map]
    change (k.mu (M ⊗ N) H).inv.val.app W
      (moduleTmul _ _ W ((k.mu M N).inv.val.app W
        (moduleTmul _ _ W ((generator f k x).hom.app W t)
          ((generator f k y).hom.app W t))) ((generator f k z).hom.app W t)) = _
    change (k.mu M N).hom.val.app W ((generator f k xy).hom.app W t) = _ at hpMN
    change (k.mu M N).hom.val.app W ((generator f k xy).hom.app W t) =
      moduleTmul _ _ W ((generator f k x).hom.app W t)
        ((generator f k y).hom.app W t) at hpMN
    rw [← hpMN, hi]
    change (k.mu (M ⊗ N) H).hom.val.app W ((generator f k l).hom.app W t) = _ at hpL
    change (k.mu (M ⊗ N) H).hom.val.app W ((generator f k l).hom.app W t) =
      moduleTmul _ _ W ((generator f k xy).hom.app W t)
        ((generator f k z).hom.app W t) at hpL
    rw [← hpL, hi]
  have halpha : l ≫ (underlying R).map (α_ M N H).hom = r := by
    apply Sheaf.hom_ext
    ext U s
    exact moduleTmul_associator M N H U _ _ _
  have hn := congrArg (fun v ↦ v.hom.app W t)
    (generator_naturality f k (α_ M N H).hom l)
  rw [halpha] at hn
  change (generator f k r).hom.app W t =
    (f.L.map (α_ M N H).hom).val.app W ((generator f k l).hom.app W t) at hn
  change (α_ (f.L.obj M) (f.L.obj N) (f.L.obj H)).hom.val.app W _ =
    (𝟙 (f.L.obj M) ⊗ₘ (k.mu N H).hom).val.app W
      ((k.mu M (N ⊗ H)).hom.val.app W
        ((f.L.map (α_ M N H).hom).val.app W (e.hom.val.app W _)))
  rw [hli, ← hn]
  change (k.mu M (N ⊗ H)).hom.val.app W ((generator f k r).hom.app W t) = _ at hpR
  change (k.mu M (N ⊗ H)).hom.val.app W ((generator f k r).hom.app W t) =
    moduleTmul _ _ W ((generator f k x).hom.app W t)
      ((generator f k yz).hom.app W t) at hpR
  rw [hpR, moduleTmul_map]
  change (k.mu N H).hom.val.app W ((generator f k yz).hom.app W t) = _ at hpNH
  change (α_ (f.L.obj M) (f.L.obj N) (f.L.obj H)).hom.val.app W _ =
    moduleTmul _ _ W ((generator f k x).hom.app W t)
      ((k.mu N H).hom.val.app W ((generator f k yz).hom.app W t))
  change (k.mu N H).hom.val.app W ((generator f k yz).hom.app W t) =
    moduleTmul _ _ W ((generator f k y).hom.app W t)
      ((generator f k z).hom.app W t) at hpNH
  rw [hpNH, moduleTmul_associator, hx, hy, hz]

end CategoryTheory.CochainPullback
