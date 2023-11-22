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

// struct Artist {
//     name: String,
// }

pub struct SVenue {
    id: usize,
    name: String,
    capacity: usize,
}

#[derive(Debug, serde::Deserialize)]
struct VenueRecord {
    name: String,
    capacity: usize,
}

pub fn load_venues<P>(path: P) -> Result<Vec<SVenue>, Box<dyn error::Error>>
where
    P: AsRef<Path>,
{
    let mut venues = vec![];
    let mut reader = csv::Reader::from_path(path)?;
    for result in reader.deserialize() {
        let record: VenueRecord = result?;

        venues.push(SVenue {
            id: venues.len(),
            name: record.name,
            capacity: record.capacity,
        })
    }

    Ok(venues)
}

struct Event {
    id: usize,
    artists: Vec<usize>,
    duration: usize,
}

impl Event {
    fn new(id: usize, artists: Vec<usize>, duration: usize) -> Self {
        Self {
            id,
            artists,
            duration,
        }
    }
}

type Interval = usize;
type Artist = usize;
type Venue = usize;
type ArtistIndex = (Interval, Venue, Artist);
type EventIndex = (Interval, Venue, usize);

pub struct Scheduler {
    start: usize,
    end: usize,
    artists: Vec<String>,
    venues: Vec<String>,
    events: Vec<Event>,
    formula: solver::Formula,
    artist_vars: HashMap<ArtistIndex, Variable>,
    event_vars: HashMap<EventIndex, Variable>,
}

impl Scheduler {
    pub fn new() -> Self {
        Self {
            start: 0,
            end: 2,
            artists: vec![
                String::from("a"),
                String::from("b"),
                String::from("c"),
                String::from("d"),
            ],
            venues: vec![String::from("v1"), String::from("v2")],
            events: vec![
                Event::new(0, vec![0, 1, 2], 8),
                Event::new(1, vec![2, 3], 8),
                Event::new(2, vec![0, 1], 8),
            ],
            formula: solver::Formula::new(),
            artist_vars: HashMap::new(),
            event_vars: HashMap::new(),
        }
    }

    // scheduler logic

    // variables
    fn add_artist_var(&mut self, interval: usize, venue: Venue, artist: Artist) -> Variable {
        let index = (interval, venue, artist);
        *self
            .artist_vars
            .entry(index)
            .or_insert(self.formula.add_var())
    }

    fn add_event_var(&mut self, interval: usize, venue: Venue, event: usize) -> Variable {
        let index = (interval, venue, event);
        *self
            .event_vars
            .entry(index)
            .or_insert(self.formula.add_var())
    }

    fn artist_var(&mut self, interval: usize, venue: Venue, artist: Artist) -> Variable {
        let index = (interval, venue, artist);
        self.artist_vars[&index]
    }

    fn event_var(&mut self, interval: usize, venue: Venue, event: usize) -> Variable {
        let index = (interval, venue, event);
        self.event_vars[&index]
    }

    fn add_artist(&mut self, artist: Artist) {
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
                let variables = (0..self.events.len())
                    .map(|event| self.event_var(interval, venue, event))
                    .collect();
                self.zero_or_one(variables);
            }
        }
    }

    fn artists_attend_events(&mut self, event: usize) {
        for interval in self.start..self.end {
            for venue in 0..self.venues.len() {
                for artist in self.events[event].artists.clone() {
                    let artist_lit = self.artist_var(interval, venue, artist);
                    let event_lit = self.event_var(interval, venue, event);
                    self.formula
                        .add_clause(vec![!event_lit.literal(), artist_lit.literal()]);
                }
            }
        }
    }

    fn artist_one_place_at_a_time(&mut self, artist: Artist) {
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

        for event in 0..self.events.len() {
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
                        for event in self.events.iter() {
                            let indices = (interval, venue, event.id);
                            let event_lit = self.event_vars[&indices];
                            match solver.value(&event_lit) {
                                Value::True => println!(
                                    "event: {} interval: {} venue: {}",
                                    event.id, interval, venue
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
                                    "artist: {} interval: {} venue: {}",
                                    artist, interval, venue
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
