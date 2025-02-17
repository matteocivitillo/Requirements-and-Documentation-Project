
abstract sig InternshipStatus {}
one sig InternshipOpen, InternshipApplied, InternshipAccepted, InternshipOngoing, InternshipClosed extends InternshipStatus {}

abstract sig ApplicationStatus {}
one sig ApplicationSubmitted, ApplicationAccepted, ApplicationRejected extends ApplicationStatus {}

abstract sig ComplaintStatus {}
one sig ComplaintOpen, ComplaintUnderReview, ComplaintResolved, ComplaintRejected extends ComplaintStatus {}

abstract sig University {}
one sig UniA, UniB, UniC extends University {}

abstract sig Field {}
one sig Engineering, Law, Medicine, ComputerScience extends Field {}

sig Email {} 

// Abstract account for common properties
abstract sig Account {
    email: one Email
}

// Student inherits from Account
sig Student extends Account {
    university: one University,
    field: one Field,
    applications: set Application,
    internships: set Internship   
}

// CompanyHR inherits from Account
sig CompanyHR extends Account {
    field: one Field,               
    posts: set Internship     
}

// UC inherits from Account
sig UC extends Account {
    complaints: set Complaint       
}
sig Internship {
    field: one Field,               
    applications: set Application,  
    has: set Feedback,              
    status: one InternshipStatus,   
    students: set Student,
    postedBy: one CompanyHR         
}

sig Application {
    student: one Student,          
    internship: one Internship,     
    status: one ApplicationStatus   
}

sig Feedback {
    givenBy: lone (Student + CompanyHR), 
    about: one Internship               
}

sig Complaint {
    submittedBy: lone (Student + CompanyHR), 
    handledBy: one UC,
    status: one ComplaintStatus,
    about: one Internship      
}



-- FACT

// Facts for Students & Companies (S&C) Platform

// -- Account:

// Ensures that each account (Student, CompanyHR, UC) has a unique email.
fact AccountUniqueEmails {
    no disj a1, a2 : Account | a1.email = a2.email
}

// Ensures that the applications of a student are consistent with the application-student relationship.
fact studentApplicationConsistency {
    all s: Student, a: Application |
        (a.student = s) iff (a in s.applications)
}

// Ensures that the internships associated with a student are correctly derived from the applications submitted by the student.
fact StudentInternshipLinkage {
    all s: Student |
        s.internships = { i: Internship | some a: Application | a.student = s and a.internship = i }
}

// -- Internship:

// Ensures that no two internships are identical by prohibiting duplicate instances.
fact InternshipNoDuplicates {
    no disj i1, i2 : Internship | i1 = i2
}

// Ensures that every internship is posted by exactly one CompanyHR or none at all.
fact InternshipPostedByCompanyHR {
    all i: Internship | lone c: CompanyHR | i in c.posts
}

// Ensures that every internship has an associated poster (a CompanyHR).
fact EveryInternshipHasPoster {
    all i: Internship | some c: CompanyHR | i in c.posts
}

// Ensures internships only have valid statuses, defined in the InternshipStatus hierarchy.
fact InternshipValidStatuses {
    all i: Internship | i.status in InternshipOpen + InternshipApplied + InternshipAccepted + InternshipOngoing + InternshipClosed
}

// Ensures that internships can transition to "Applied" status only if they have at least one application.
fact InternshipTransitionToApplied {
    all i: Internship | i.status = InternshipApplied iff some i.applications
}

// Ensures that internships can transition to "Ongoing" status only if they have at least one accepted application.
fact InternshipTransitionToOngoing {
    all i: Internship | i.status = InternshipOngoing implies some 
	a: i.applications | a.status = ApplicationAccepted
}

// Ensures that a closed internship cannot have any pending applications.
fact InternshipClosed {
    all i: Internship | i.status = InternshipClosed implies no a: i.applications | a.status = ApplicationSubmitted
}

// Ensures that the status of an internship is consistent with the status of its applications.
fact internshipStatusConsistency {
    all i: Internship |
        (all a: i.applications | a.status = ApplicationRejected) implies i.status != InternshipApplied
}

// Ensures that students accepted to an internship are correctly linked to that internship.
fact AcceptedStudentsLinkedToInternship {
    all i: Internship | 
        i.students = {s: Student | some a: Application | a.student = s and a.internship = i and a.status = ApplicationAccepted}
}

// Ensures that feedback is linked to the internship it is about and given by a valid entity (Student or CompanyHR).
fact FeedbackLinkage {
    all f: Feedback |
        ((f.givenBy in Student) => f.about in f.givenBy.internships)
        and
        ((f.givenBy in CompanyHR) => f.about in f.givenBy.posts)
}

// Ensures that complaints are linked to the internships they are about and submitted by valid entities.
fact ComplaintLinkage {
    all c: Complaint |
        ((c.submittedBy in Student) => c.about in c.submittedBy.internships)
        and
        ((c.submittedBy in CompanyHR) => c.about in c.submittedBy.posts)
}

// Ensures that internships in the "Accepted" status have at least one accepted application.
fact InternshipAcceptedCondition {
    all i: Internship |
        (i.status = InternshipAccepted) =>
        some a: i.applications | a.status = ApplicationAccepted
}

// Ensures that each internship is correctly listed as a post of the CompanyHR who posted it.
fact InternshipPostedByHR {
    all i: Internship | i in i.postedBy.posts
}

// Ensures that internships with feedback or complaints must have at least one application.
fact InternshipWithFeedbackOrComplaintHasApplications {
    all i: Internship |
        ((some i.has) or (some c: Complaint | c.about = i)) implies some i.applications
}

// -- Application:

// Ensures that no two applications are identical by prohibiting duplicate instances.
fact ApplicationNoDuplicates {
    no disj a1, a2 : Application | a1 = a2
}

// Ensures that applications only have valid statuses, defined in the ApplicationStatus hierarchy.
fact ApplicationValidStatuses {
    all a: Application | a.status in ApplicationSubmitted + ApplicationAccepted + ApplicationRejected
}

// Ensures that each application is correctly linked to an internship, and that it is part of the internship's set of applications.
fact ApplicationBelongingToInternship {
    all a: Application | a in a.internship.applications
}

// Ensures that an application can belong to only one internship.
fact applicationBelongsToSingleInternship {
    all a: Application |
        lone i: Internship | a in i.applications
}

// -- Feedback:

// Ensures that feedback is provided by either a Student or a CompanyHR, but not both.
fact FeedbackOwnership {
    all f: Feedback | some f.givenBy and f.givenBy in (Student + CompanyHR)
}

// Ensures that feedback is correctly linked to an internship and included in its set of feedback.
fact FeedbackBelongingToInternship {
    all f: Feedback | f in f.about.has
}

// -- Complaint:

// Ensures that no two complaints are identical by prohibiting duplicate instances.
fact ComplaintNoDuplicates {
    no disj c1, c2 : Complaint | c1 = c2
}

// Ensures that complaints only have valid statuses, defined in the ComplaintStatus hierarchy.
fact ComplaintValidStatuses {
    all c: Complaint | c.status in ComplaintOpen + ComplaintUnderReview + ComplaintResolved + ComplaintRejected
}

// Ensures that complaints are submitted by valid entities (either a Student or a CompanyHR).
fact ComplaintSubmittedByValidEntity {
    all c: Complaint | c.submittedBy in (Student + CompanyHR)
}

// Ensures that an open complaint has not been assigned to a University Coordinator (UC), and assigned complaints are under review.
fact complaintStateAndAssignment {
    all c: Complaint |
        (c.status = ComplaintOpen implies no c.handledBy) and
        (some c.handledBy implies c.status = ComplaintUnderReview)
}

// -- Status Transitions:

// Ensures internships follow logical lifecycle transitions: Open → Applied → Accepted → Ongoing → Closed.
fact InternshipLifecycle {
    all i: Internship | 
        (i.status = InternshipApplied implies some i.applications) and
        (i.status = InternshipOngoing implies some a: i.applications | a.status = ApplicationAccepted) and
        (i.status = InternshipClosed implies no i.applications)
}

// Ensures applications follow logical lifecycle transitions: Submitted → Accepted/Rejected.
fact ApplicationLifecycle {
    all a: Application | 
        (a.status = ApplicationSubmitted or 
         a.status = ApplicationAccepted or 
         a.status = ApplicationRejected)
}

// Ensures complaints follow logical lifecycle transitions: Open → UnderReview → Resolved/Rejected.
fact ComplaintLifecycle {
    all c: Complaint | 
        (c.status = ComplaintOpen or 
         (c.status = ComplaintUnderReview and some c.handledBy) or 
         c.status = ComplaintResolved or 
         c.status = ComplaintRejected)
}




// Assertions and Predicates for Students & Companies (S&C) Platform

// -- Assertions:

// Ensures that all applications are associated with an internship,
// and the application exists in the internship's set of applications.
assert validApplications {
    all a: Application | a.internship in Internship and a in a.internship.applications
}
check validApplications

// Ensures that all feedback entries are linked to an internship,
// and that the internship includes them in its feedback set.
assert validFeedback {
    all f: Feedback | f.about in Internship and f in f.about.has
}
check validFeedback

// Ensures that all complaints are handled by a university coordinator.
assert complaintsHandledByUC {
    all c: Complaint | some c.handledBy
}
check complaintsHandledByUC

// Ensures that internships transition between valid statuses based on the conditions defined in the facts.
assert internshipLifecycleValid {
    all i: Internship | 
        (i.status = InternshipApplied implies some i.applications) and
        (i.status = InternshipOngoing implies some a: Application | a in i.applications and a.status = ApplicationAccepted) and
        (i.status = InternshipClosed implies no a: Application | a in i.applications)
}
check internshipLifecycleValid

// Ensures that applications transition between valid statuses (Submitted → Accepted/Rejected).
assert applicationLifecycleValid {
    all a: Application | 
        (a.status = ApplicationSubmitted or 
         a.status = ApplicationAccepted or 
         a.status = ApplicationRejected)
}
check applicationLifecycleValid

// Ensures that all feedback is provided by either a student or a company HR, but not both.
assert feedbackGivenByValidEntities {
    all f: Feedback | some f.givenBy and f.givenBy in (Student + CompanyHR)
}
check feedbackGivenByValidEntities

// Ensures that complaints transition between valid statuses (Open → UnderReview → Resolved/Rejected).
assert complaintLifecycleValid {
    all c: Complaint | 
        (c.status = ComplaintOpen or 
         (c.status = ComplaintUnderReview and some c.handledBy) or 
         c.status = ComplaintResolved or 
         c.status = ComplaintRejected)
}
check complaintLifecycleValid

// Ensures that no applications can be submitted to an internship if its status is Closed.
assert noApplicationToClosedInternship {
    all i: Internship | 
        (i.status = InternshipClosed implies no a: Application | a.internship = i and a.status = ApplicationSubmitted)
}
check noApplicationToClosedInternship

// Ensures that all complaints in the system are handled by a University Coordinator (UC).
assert allComplaintsHandled {
    all c: Complaint |
        some c.handledBy
}
check allComplaintsHandled

// Ensures that all feedback is provided by a valid entity, either a Student or a CompanyHR.
assert feedbackGivenByValidAccount {
    all f: Feedback |
        some f.givenBy and f.givenBy in (Student + CompanyHR)
}
check feedbackGivenByValidAccount

// Ensures that all internships with the status "Ongoing" have at least one accepted application.
assert ongoingInternshipsHaveAcceptedApplications {
    all i: Internship |
        (i.status = InternshipOngoing implies some a: Application | a.internship = i and a.status = ApplicationAccepted)
}
check ongoingInternshipsHaveAcceptedApplications

// Ensures complaints cannot be Resolved or Rejected unless they have been UnderReview.
assert complaintResolutionAfterReview {
    all c: Complaint |
        (c.status = ComplaintResolved or c.status = ComplaintRejected) implies 
        (c.status = ComplaintUnderReview or c.status = ComplaintOpen)
}
check complaintResolutionAfterReview

// Ensures that an open complaint has not yet been assigned to a University Coordinator (UC).
assert openComplaintUnassigned {
    all c: Complaint |
        (c.status = ComplaintOpen implies no c.handledBy)
}
check openComplaintUnassigned

// Ensures that complaints under review are always handled by a University Coordinator.
assert underReviewComplaintAssigned {
    all c: Complaint |
        (c.status = ComplaintUnderReview implies some c.handledBy)
}
check underReviewComplaintAssigned

// Ensures that an accepted application cannot later be rejected.
assert noRejectionAfterAcceptance {
    all a: Application |
        (a.status = ApplicationAccepted implies not (a.status = ApplicationRejected))
}
check noRejectionAfterAcceptance

// Ensures all feedback is provided by a valid entity and linked to a valid internship.
assert feedbackLinkedToValidEntities {
    all f: Feedback |
        (some f.givenBy and f.about in Internship)
}
check feedbackLinkedToValidEntities

// Ensures that open complaints are unassigned and assigned complaints are UnderReview.
assert complaintOpenOrUnderReview {
    all c: Complaint |
        (c.status = ComplaintOpen implies no c.handledBy) and
        (some c.handledBy implies c.status = ComplaintUnderReview)
}
check complaintOpenOrUnderReview

// Ensures that all feedback entries are connected to an internship.
assert allFeedbackLinkedToInternships {
    all f: Feedback | some f.about
}
check allFeedbackLinkedToInternships

// Ensures that internships in the "Open" status have no applications or only rejected applications.
assert internshipOpenCondition {
    all i: Internship |
        (i.status = InternshipOpen) =>
        (no i.applications or all a: i.applications | a.status = ApplicationRejected)
}
check internshipOpenCondition

// Ensures that internships in the "Accepted" status have at least one accepted application.
assert internshipAcceptedCondition {
    all i: Internship |
        (i.status = InternshipAccepted) =>
        (some a: i.applications | a.status = ApplicationAccepted)
}
check internshipAcceptedCondition

// Ensures that internships in the "Ongoing" status have at least one accepted application.
assert internshipOngoingCondition {
    all i: Internship |
        (i.status = InternshipOngoing) =>
        some a: i.applications | a.status = ApplicationAccepted
}
check internshipOngoingCondition

// Ensures that internships in the "Closed" status have no pending applications.
assert internshipClosedCondition {
    all i: Internship |
        (i.status = InternshipClosed) =>
        no a: i.applications | a.status = ApplicationSubmitted
}
check internshipClosedCondition

// -- Predicates:

// Generates a complete world with multiple students, companies, internships, applications, feedback, and complaints.
pred completeWorld {
    some s: Student, c: CompanyHR, i: Internship, a: Application, f: Feedback, comp: Complaint, uc: UC |
        a.student = s and
        a.internship = i and
        i in c.posts and
        f.about = i and
        comp.handledBy = uc
}
run completeWorld for 5
















