//signatures
abstract sig Account {
  name: one Name,
  surname: one Surname,
  username: one Username,
  email: one Email,
  password: one Password
}

sig Name {
}{
  no n : Name | n. ~name  = none
}

sig Surname {
}{
  no s : Surname  | s. ~surname = none
}

sig Email {}
{
  no disj a1, a2 : Account | a1.email = a2.email
  no e: Email | e. ~email = none
}

sig Username {}
{
  no disj a1, a2 : Account | a1.username = a2.username
  no u: Username | u.~username = none
}

sig Password {
} {
  no p: Password | p. ~password = none
}

sig Farm {
  area: one Area
} {
  #this.~inspection >= 2
}

sig Post {
} 

sig DailyPlan {
  visits: set Visit
} {
  #visits>=2
}

sig Visit {
  inspection: one Farm
}  

one sig DashBoard {
  farms_dashboard: set Farm
}

sig Thread {
  posts: some Post,
}

one sig Forum {
  threads: set Thread,
}

sig Area {
  farms:set Farm,
}

sig PolicyMaker extends Account {
  dashboard: one DashBoard,
}

sig Farmer extends Account {
  farm: one Farm,
  forumF: one Forum,
  requests : set HelpRequest
}

sig Agronomist extends Account {
  forumA: one Forum,
  areas: one Area,
         dashboard: one DashBoard,
  dailyplan: one DailyPlan
}

sig HelpRequest{
  agronomist : one Agronomist
}{
  no h: HelpRequest | h. ~requests = none
}

//facts
fact aboutThread {
  posts in Thread one -> Post
}

fact aboutDashBoard {
  farms_dashboard in DashBoard one -> Farm
}

fact aboutForum {
  threads in Forum one -> Thread
  forumA in Agronomist some -> Forum
  forumF in Farmer  some -> Forum
}

fact aboutFarms {
  visits in DailyPlan one -> Visit
  farm in Farmer one -> Farm
  area = ~farms
}

fact aboutAgron {
  areas in Agronomist one -> Area
  dailyplan in Agronomist one -> DailyPlan
  visits in DailyPlan one -> Visit
}

fact aboutArea {
  farms in Area one -> Farm 
}

fact aboutDailyPlan{
  all d:DailyPlan | d.visits.inspection.area = d. ~dailyplan.areas
}

fact aboutHelpRequest{
  all h: HelpRequest | h.agronomist.areas = h. ~requests.farm.area
  no disj f1, f2: Farmer | f1.requests = f2.requests
}

//asserts
assert agronomistArea {
  no disj a1, a2: Agronomist | {
    a1.areas = a2.areas
  }
}

//check agronomistArea for 10

assert helpRequest {
  all a1, a2: Agronomist, f: Farmer, disj h1, h2: HelpRequest | {
    (h1.~requests = f and h2.~requests = f and a1.~agronomist = h1 and a2.~agronomist = h2) implies (a1=a2) 
  }
}

//check helpRequest for 10

assert dailyPlan {
  all a1, a2: Area, disj v1, v2: Visit | {
    (v1.inspection.area = a1 and v2.inspection.area = a2 and v1.~visits.~dailyplan = v2.~visits.~dailyplan) implies (a1 = a2)
  }
}

//check dailyPlan for 10

//predicates
pred world1 {
  # Account = 5
  # Agronomist = 2
  # PolicyMaker = 0
  # Farmer = 3
}
run world1 for 6

/*pred world1 {
  # Account = 5
  # Farmer = 3
  # Agronomist = 2
}
run world1 for 6*/
