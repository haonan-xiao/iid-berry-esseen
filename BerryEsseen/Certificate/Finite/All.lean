import BerryEsseen.Certificate.Finite.Data.N001
import BerryEsseen.Certificate.Finite.Data.N002
import BerryEsseen.Certificate.Finite.Data.N003
import BerryEsseen.Certificate.Finite.Data.N004
import BerryEsseen.Certificate.Finite.Data.N005
import BerryEsseen.Certificate.Finite.Data.N006
import BerryEsseen.Certificate.Finite.Data.N007
import BerryEsseen.Certificate.Finite.Data.N008
import BerryEsseen.Certificate.Finite.Data.N009
import BerryEsseen.Certificate.Finite.Data.N010
import BerryEsseen.Certificate.Finite.Batches.Batch01
import BerryEsseen.Certificate.Finite.Batches.Batch02
import BerryEsseen.Certificate.Finite.Batches.Batch03
import BerryEsseen.Certificate.Finite.Batches.Batch04
import BerryEsseen.Certificate.Finite.Batches.Batch05
import BerryEsseen.Certificate.Finite.Batches.Batch06
import BerryEsseen.Certificate.Finite.Batches.Batch07
import BerryEsseen.Certificate.Finite.Batches.Batch08
/-!
# Complete finite-`n` Route B leaf certificates

For every integer `1 ≤ n < 100`, this module selects a concrete prefix-code
certificate.  Each imported certificate is recomputed by Lean with
`native_decide`; the external code generator is not part of the trusted base.
-/

namespace BerryEsseen

/-- The complete finite branch required by the Route B numerical assembly. -/
theorem routeB_finiteLeafCertificates_checked
    (n : ℕ) (hn1 : 1 ≤ n) (hn100 : n < 100) :
    ∃ code : String, dyadicRouteBLeafCodeCertificate n code = true := by
  interval_cases n
  · exact ⟨dyadicRouteBLeafCode01, dyadicRouteBLeafCodeCertificate_one⟩
  · exact ⟨dyadicRouteBLeafCode02, dyadicRouteBLeafCodeCertificate_two⟩
  · exact ⟨dyadicRouteBLeafCode03, dyadicRouteBLeafCodeCertificate_n03⟩
  · exact ⟨dyadicRouteBLeafCode04, dyadicRouteBLeafCodeCertificate_n04⟩
  · exact ⟨dyadicRouteBLeafCode05, dyadicRouteBLeafCodeCertificate_n05⟩
  · exact ⟨dyadicRouteBLeafCode06, dyadicRouteBLeafCodeCertificate_n06⟩
  · exact ⟨dyadicRouteBLeafCode07, dyadicRouteBLeafCodeCertificate_n07⟩
  · exact ⟨dyadicRouteBLeafCode08, dyadicRouteBLeafCodeCertificate_n08⟩
  · exact ⟨dyadicRouteBLeafCode09, dyadicRouteBLeafCodeCertificate_n09⟩
  · exact ⟨dyadicRouteBLeafCode10, dyadicRouteBLeafCodeCertificate_n10⟩
  · exact ⟨dyadicRouteBLeafCode11, dyadicRouteBLeafCodeCertificate_n11⟩
  · exact ⟨dyadicRouteBLeafCode12, dyadicRouteBLeafCodeCertificate_n12⟩
  · exact ⟨dyadicRouteBLeafCode13, dyadicRouteBLeafCodeCertificate_n13⟩
  · exact ⟨dyadicRouteBLeafCode14, dyadicRouteBLeafCodeCertificate_n14⟩
  · exact ⟨dyadicRouteBLeafCode15, dyadicRouteBLeafCodeCertificate_n15⟩
  · exact ⟨dyadicRouteBLeafCode16, dyadicRouteBLeafCodeCertificate_n16⟩
  · exact ⟨dyadicRouteBLeafCode17, dyadicRouteBLeafCodeCertificate_n17⟩
  · exact ⟨dyadicRouteBLeafCode18, dyadicRouteBLeafCodeCertificate_n18⟩
  · exact ⟨dyadicRouteBLeafCode19, dyadicRouteBLeafCodeCertificate_n19⟩
  · exact ⟨dyadicRouteBLeafCode20, dyadicRouteBLeafCodeCertificate_n20⟩
  · exact ⟨dyadicRouteBLeafCode21, dyadicRouteBLeafCodeCertificate_n21⟩
  · exact ⟨dyadicRouteBLeafCode22, dyadicRouteBLeafCodeCertificate_n22⟩
  · exact ⟨dyadicRouteBLeafCode23, dyadicRouteBLeafCodeCertificate_n23⟩
  · exact ⟨dyadicRouteBLeafCode24, dyadicRouteBLeafCodeCertificate_n24⟩
  · exact ⟨dyadicRouteBLeafCode25, dyadicRouteBLeafCodeCertificate_n25⟩
  · exact ⟨dyadicRouteBLeafCode26, dyadicRouteBLeafCodeCertificate_n26⟩
  · exact ⟨dyadicRouteBLeafCode27, dyadicRouteBLeafCodeCertificate_n27⟩
  · exact ⟨dyadicRouteBLeafCode28, dyadicRouteBLeafCodeCertificate_n28⟩
  · exact ⟨dyadicRouteBLeafCode29, dyadicRouteBLeafCodeCertificate_n29⟩
  · exact ⟨dyadicRouteBLeafCode30, dyadicRouteBLeafCodeCertificate_n30⟩
  · exact ⟨dyadicRouteBLeafCode31, dyadicRouteBLeafCodeCertificate_n31⟩
  · exact ⟨dyadicRouteBLeafCode32, dyadicRouteBLeafCodeCertificate_n32⟩
  · exact ⟨dyadicRouteBLeafCode33, dyadicRouteBLeafCodeCertificate_n33⟩
  · exact ⟨dyadicRouteBLeafCode34, dyadicRouteBLeafCodeCertificate_n34⟩
  · exact ⟨dyadicRouteBLeafCode35, dyadicRouteBLeafCodeCertificate_n35⟩
  · exact ⟨dyadicRouteBLeafCode36, dyadicRouteBLeafCodeCertificate_n36⟩
  · exact ⟨dyadicRouteBLeafCode37, dyadicRouteBLeafCodeCertificate_n37⟩
  · exact ⟨dyadicRouteBLeafCode38, dyadicRouteBLeafCodeCertificate_n38⟩
  · exact ⟨dyadicRouteBLeafCode39, dyadicRouteBLeafCodeCertificate_n39⟩
  · exact ⟨dyadicRouteBLeafCode40, dyadicRouteBLeafCodeCertificate_n40⟩
  · exact ⟨dyadicRouteBLeafCode41, dyadicRouteBLeafCodeCertificate_n41⟩
  · exact ⟨dyadicRouteBLeafCode42, dyadicRouteBLeafCodeCertificate_n42⟩
  · exact ⟨dyadicRouteBLeafCode43, dyadicRouteBLeafCodeCertificate_n43⟩
  · exact ⟨dyadicRouteBLeafCode44, dyadicRouteBLeafCodeCertificate_n44⟩
  · exact ⟨dyadicRouteBLeafCode45, dyadicRouteBLeafCodeCertificate_n45⟩
  · exact ⟨dyadicRouteBLeafCode46, dyadicRouteBLeafCodeCertificate_n46⟩
  · exact ⟨dyadicRouteBLeafCode47, dyadicRouteBLeafCodeCertificate_n47⟩
  · exact ⟨dyadicRouteBLeafCode48, dyadicRouteBLeafCodeCertificate_n48⟩
  · exact ⟨dyadicRouteBLeafCode49, dyadicRouteBLeafCodeCertificate_n49⟩
  · exact ⟨dyadicRouteBLeafCode50, dyadicRouteBLeafCodeCertificate_n50⟩
  · exact ⟨dyadicRouteBLeafCode51, dyadicRouteBLeafCodeCertificate_n51⟩
  · exact ⟨dyadicRouteBLeafCode52, dyadicRouteBLeafCodeCertificate_n52⟩
  · exact ⟨dyadicRouteBLeafCode53, dyadicRouteBLeafCodeCertificate_n53⟩
  · exact ⟨dyadicRouteBLeafCode54, dyadicRouteBLeafCodeCertificate_n54⟩
  · exact ⟨dyadicRouteBLeafCode55, dyadicRouteBLeafCodeCertificate_n55⟩
  · exact ⟨dyadicRouteBLeafCode56, dyadicRouteBLeafCodeCertificate_n56⟩
  · exact ⟨dyadicRouteBLeafCode57, dyadicRouteBLeafCodeCertificate_n57⟩
  · exact ⟨dyadicRouteBLeafCode58, dyadicRouteBLeafCodeCertificate_n58⟩
  · exact ⟨dyadicRouteBLeafCode59, dyadicRouteBLeafCodeCertificate_n59⟩
  · exact ⟨dyadicRouteBLeafCode60, dyadicRouteBLeafCodeCertificate_n60⟩
  · exact ⟨dyadicRouteBLeafCode61, dyadicRouteBLeafCodeCertificate_n61⟩
  · exact ⟨dyadicRouteBLeafCode62, dyadicRouteBLeafCodeCertificate_n62⟩
  · exact ⟨dyadicRouteBLeafCode63, dyadicRouteBLeafCodeCertificate_n63⟩
  · exact ⟨dyadicRouteBLeafCode64, dyadicRouteBLeafCodeCertificate_n64⟩
  · exact ⟨dyadicRouteBLeafCode65, dyadicRouteBLeafCodeCertificate_n65⟩
  · exact ⟨dyadicRouteBLeafCode66, dyadicRouteBLeafCodeCertificate_n66⟩
  · exact ⟨dyadicRouteBLeafCode67, dyadicRouteBLeafCodeCertificate_n67⟩
  · exact ⟨dyadicRouteBLeafCode68, dyadicRouteBLeafCodeCertificate_n68⟩
  · exact ⟨dyadicRouteBLeafCode69, dyadicRouteBLeafCodeCertificate_n69⟩
  · exact ⟨dyadicRouteBLeafCode70, dyadicRouteBLeafCodeCertificate_n70⟩
  · exact ⟨dyadicRouteBLeafCode71, dyadicRouteBLeafCodeCertificate_n71⟩
  · exact ⟨dyadicRouteBLeafCode72, dyadicRouteBLeafCodeCertificate_n72⟩
  · exact ⟨dyadicRouteBLeafCode73, dyadicRouteBLeafCodeCertificate_n73⟩
  · exact ⟨dyadicRouteBLeafCode74, dyadicRouteBLeafCodeCertificate_n74⟩
  · exact ⟨dyadicRouteBLeafCode75, dyadicRouteBLeafCodeCertificate_n75⟩
  · exact ⟨dyadicRouteBLeafCode76, dyadicRouteBLeafCodeCertificate_n76⟩
  · exact ⟨dyadicRouteBLeafCode77, dyadicRouteBLeafCodeCertificate_n77⟩
  · exact ⟨dyadicRouteBLeafCode78, dyadicRouteBLeafCodeCertificate_n78⟩
  · exact ⟨dyadicRouteBLeafCode79, dyadicRouteBLeafCodeCertificate_n79⟩
  · exact ⟨dyadicRouteBLeafCode80, dyadicRouteBLeafCodeCertificate_n80⟩
  · exact ⟨dyadicRouteBLeafCode81, dyadicRouteBLeafCodeCertificate_n81⟩
  · exact ⟨dyadicRouteBLeafCode82, dyadicRouteBLeafCodeCertificate_n82⟩
  · exact ⟨dyadicRouteBLeafCode83, dyadicRouteBLeafCodeCertificate_n83⟩
  · exact ⟨dyadicRouteBLeafCode84, dyadicRouteBLeafCodeCertificate_n84⟩
  · exact ⟨dyadicRouteBLeafCode85, dyadicRouteBLeafCodeCertificate_n85⟩
  · exact ⟨dyadicRouteBLeafCode86, dyadicRouteBLeafCodeCertificate_n86⟩
  · exact ⟨dyadicRouteBLeafCode87, dyadicRouteBLeafCodeCertificate_n87⟩
  · exact ⟨dyadicRouteBLeafCode88, dyadicRouteBLeafCodeCertificate_n88⟩
  · exact ⟨dyadicRouteBLeafCode89, dyadicRouteBLeafCodeCertificate_n89⟩
  · exact ⟨dyadicRouteBLeafCode90, dyadicRouteBLeafCodeCertificate_n90⟩
  · exact ⟨dyadicRouteBLeafCode91, dyadicRouteBLeafCodeCertificate_n91⟩
  · exact ⟨dyadicRouteBLeafCode92, dyadicRouteBLeafCodeCertificate_n92⟩
  · exact ⟨dyadicRouteBLeafCode93, dyadicRouteBLeafCodeCertificate_n93⟩
  · exact ⟨dyadicRouteBLeafCode94, dyadicRouteBLeafCodeCertificate_n94⟩
  · exact ⟨dyadicRouteBLeafCode95, dyadicRouteBLeafCodeCertificate_n95⟩
  · exact ⟨dyadicRouteBLeafCode96, dyadicRouteBLeafCodeCertificate_n96⟩
  · exact ⟨dyadicRouteBLeafCode97, dyadicRouteBLeafCodeCertificate_n97⟩
  · exact ⟨dyadicRouteBLeafCode98, dyadicRouteBLeafCodeCertificate_n98⟩
  · exact ⟨dyadicRouteBLeafCode99, dyadicRouteBLeafCodeCertificate_n99⟩

end BerryEsseen
