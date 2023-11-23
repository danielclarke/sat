use crate::{
    solver::{self, Solution, Value, Variable},
    utils::read_lines,
};
use std::collections::HashMap;
use std::path::Path;
use std::{error, fmt};

#[derive(Debug, Clone)]
pub enum DataError {
    EmptyFile,
}

impl fmt::Display for DataError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            DataError::EmptyFile => write!(f, "Empty file"),
        }
    }
}

impl error::Error for DataError {}

#[derive(Debug)]
pub struct Artist {
    id: usize,
    name: String,
}

pub fn load_artists<P>(path: P) -> Result<Vec<Artist>, Box<dyn error::Error>>
where
    P: AsRef<Path>,
{
    let mut artist_names = vec![];
    let mut reader = csv::Reader::from_path(path)?;
    for result in reader.deserialize() {
        let EventRecord {
            session_title: _,
            session_chair,
            participants,
        } = result?;
        artist_names.append(
            &mut participants
                .split('\n')
                .map(|s| s.trim().to_owned())
                .collect::<Vec<_>>(),
        );
        if let Some(session_chair) = session_chair {
            artist_names.push(session_chair)
        }
    }

    artist_names.sort();
    artist_names.dedup();
    let mut artists = vec![];
    for artist_name in artist_names {
        artists.push(Artist {
            id: artists.len(),
            name: artist_name,
        });
    }

    Ok(artists)
}

pub struct Venue {
    id: usize,
    name: String,
    capacity: usize,
}

#[derive(Debug, serde::Deserialize)]
struct VenueRecord {
    name: String,
    capacity: usize,
}

pub fn load_venues<P>(path: P) -> Result<Vec<Venue>, Box<dyn error::Error>>
where
    P: AsRef<Path>,
{
    let mut venues = vec![];
    let mut reader = csv::Reader::from_path(path)?;
    for result in reader.deserialize() {
        let VenueRecord { name, capacity } = result?;

        venues.push(Venue {
            id: venues.len(),
            name,
            capacity,
        })
    }

    Ok(venues)
}

#[derive(Debug, Clone)]
pub struct Event {
    id: usize,
    name: String,
    artists: Vec<String>,
    duration: usize,
    capacity: usize,
}

#[derive(Debug, serde::Deserialize)]
struct EventRecord {
    session_title: String,
    session_chair: Option<String>,
    participants: String,
}

pub fn load_events<P>(path: P) -> Result<Vec<Event>, Box<dyn error::Error>>
where
    P: AsRef<Path>,
{
    let mut events = vec![];
    let mut reader = csv::Reader::from_path(path)?;
    for result in reader.deserialize() {
        let EventRecord {
            session_title,
            session_chair,
            participants,
        } = result?;
        let mut artists = participants
            .split('\n')
            .map(|s| s.trim().to_owned())
            .collect::<Vec<_>>();
        if let Some(session_chair) = session_chair {
            artists.push(session_chair)
        }

        events.push(Event {
            id: events.len(),
            name: session_title,
            artists,
            duration: 1,
            capacity: 100,
        })
    }

    Ok(events)
}

struct EventRep {
    id: usize,
    artists: Vec<usize>,
    duration: usize,
}

impl EventRep {
    fn new(id: usize, artists: Vec<usize>, duration: usize) -> Self {
        Self {
            id,
            artists,
            duration,
        }
    }
}

type Interval = usize;
type ArtistIndex = usize;
type VenueIndex = usize;
type ArtistVariableIndex = (Interval, VenueIndex, ArtistIndex);
type EventVariableIndex = (Interval, VenueIndex, usize);

pub struct Scheduler {
    start: usize,
    end: usize,
    artists: Vec<Artist>,
    venues: Vec<Venue>,
    events: Vec<Event>,
    event_reps: Vec<EventRep>,
    formula: solver::Formula,
    artist_vars: HashMap<ArtistVariableIndex, Variable>,
    event_vars: HashMap<EventVariableIndex, Variable>,
}

impl Scheduler {
    pub fn new(
        start: usize,
        end: usize,
        artists: Vec<Artist>,
        venues: Vec<Venue>,
        events: Vec<Event>,
    ) -> Self {
        let mut events_ = vec![];
        for event in events.iter() {
            let artist_ids = event
                .artists
                .iter()
                .map(|artist_name| {
                    artists
                        .iter()
                        .find(|&artist| artist.name == *artist_name)
                        .unwrap()
                        .id
                })
                .collect::<Vec<_>>();
            events_.push(EventRep::new(event.id, artist_ids, event.duration));
        }

        Self {
            start,
            end,
            artists,
            venues,
            events,
            event_reps: events_,
            formula: solver::Formula::new(),
            artist_vars: HashMap::new(),
            event_vars: HashMap::new(),
        }
    }

    // scheduler logic

    // variables
    fn add_artist_var(
        &mut self,
        interval: usize,
        venue: VenueIndex,
        artist: ArtistIndex,
    ) -> Variable {
        let index = (interval, venue, artist);
        *self
            .artist_vars
            .entry(index)
            .or_insert(self.formula.add_var())
    }

    fn add_event_var(&mut self, interval: usize, venue: VenueIndex, event: usize) -> Variable {
        let index = (interval, venue, event);
        *self
            .event_vars
            .entry(index)
            .or_insert(self.formula.add_var())
    }

    fn artist_var(&mut self, interval: usize, venue: VenueIndex, artist: ArtistIndex) -> Variable {
        let index = (interval, venue, artist);
        self.artist_vars[&index]
    }

    fn event_var(&mut self, interval: usize, venue: VenueIndex, event: usize) -> Variable {
        let index = (interval, venue, event);
        self.event_vars[&index]
    }

    fn add_artist(&mut self, artist: ArtistIndex) {
        for interval in self.start..self.end {
            for venue in 0..self.venues.len() {
                self.add_artist_var(interval, venue, artist);
            }
        }
    }

    fn add_event(&mut self, event: usize) {
        for interval in self.start..self.end {
            for venue in 0..self.venues.len() {
                self.add_event_var(interval, venue, event);
            }
        }
    }

    // constraints
    fn event_must_run(&mut self, event: usize) {
        let mut variables = vec![];
        for interval in self.start..self.end {
            for venue in 0..self.venues.len() {
                variables.push(self.event_var(interval, venue, event));
            }
        }
        self.exactly_one(variables);
    }

    fn one_event_per_venue_interval(&mut self) {
        for interval in self.start..self.end {
            for venue in 0..self.venues.len() {
                let variables = (0..self.event_reps.len())
                    .map(|event| self.event_var(interval, venue, event))
                    .collect();
                self.zero_or_one(variables);
            }
        }
    }

    fn artists_attend_events(&mut self, event: usize) {
        for interval in self.start..self.end {
            for venue in 0..self.venues.len() {
                for artist in self.event_reps[event].artists.clone() {
                    let artist_lit = self.artist_var(interval, venue, artist);
                    let event_lit = self.event_var(interval, venue, event);
                    self.formula
                        .add_clause(vec![!event_lit.literal(), artist_lit.literal()]);
                }
            }
        }
    }

    fn artist_one_place_at_a_time(&mut self, artist: ArtistIndex) {
        for interval in self.start..self.end {
            let variables = (0..self.venues.len())
                .map(|venue| self.artist_var(interval, venue, artist))
                .collect();
            self.zero_or_one(variables);
        }
    }

    // solve
    pub fn solve(&mut self) {
        for artist in 0..self.artists.len() {
            self.add_artist(artist);
            self.artist_one_place_at_a_time(artist);
        }

        for event in 0..self.event_reps.len() {
            self.add_event(event);
            self.artists_attend_events(event);
            self.event_must_run(event);
        }

        self.one_event_per_venue_interval();

        let mut solver = solver::Solver::new(self.formula.clone());

        match solver.solve() {
            Solution::Sat => {
                println!("SOLVED!");

                for interval in self.start..self.end {
                    for venue in 0..self.venues.len() {
                        for event in 0..self.event_reps.len() {
                            let indices = (interval, venue, event);
                            let event_lit = self.event_vars[&indices];
                            match solver.value(&event_lit) {
                                Value::True => println!(
                                    "event: {} venue: {} interval: {}",
                                    self.events[event].name, self.venues[venue].name, interval
                                ),
                                Value::Unknown => (),
                                Value::False => (),
                            }
                        }
                        for artist in 0..self.artists.len() {
                            let indices = (interval, venue, artist);
                            let artist_lit = self.artist_vars[&indices];
                            match solver.value(&artist_lit) {
                                Value::True => println!(
                                    "artist: {} venue: {} interval: {}",
                                    self.artists[artist].name, self.venues[venue].name, interval
                                ),
                                Value::Unknown => (),
                                Value::False => (),
                            }
                        }
                    }
                }
            }
            Solution::UnSat => println!("Unsat!"),
            Solution::Unknown => println!("Unknown!"),
        }
    }

    // solver helpers

    fn exactly_one(&mut self, variables: Vec<Variable>) {
        for i in 0..variables.len() {
            for j in i + 1..variables.len() {
                self.formula
                    .add_clause(vec![!variables[i].literal(), !variables[j].literal()]);
            }
        }
        self.formula
            .add_clause(variables.iter().map(|v| v.literal()).collect());
    }

    fn zero_or_one(&mut self, variables: Vec<Variable>) {
        for i in 0..variables.len() {
            for j in i + 1..variables.len() {
                self.formula
                    .add_clause(vec![!variables[i].literal(), !variables[j].literal()]);
            }
        }
    }
}
