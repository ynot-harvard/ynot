class Dept { }

class Faculty { 
    String name;
    int id;
}

class Student {
    String name;
    int id;

    Dept major;

    int numTaking; 
    Course[] taking; 

    int numTaken; 
    TranscriptEntry[] transcript; 

    Student(String n, int ssn, Dept m) {
	name = n;
	id = ssn;
	major = m;
	numTaking = 0;
	numTaken = 0;
	taking = new Course[3];
	transcript = new TranscriptEntry[30];
    }
}

class Course {
    Dept major;
    Faculty teacher;

    int numEnrolled;
    Student[] enrolled; 

    int numWaiting;
    Student[] waiting; 

    Course(Dept d, Faculty t, int limit) {
	major = d;
	teacher = t;
	numEnrolled = 0;
	numWaiting = 0;
	enrolled  = new Student[limit];
	waiting  = new Student[limit];
    }

    void addCourse(Student s) {
	if (major != s.major) return;
	if (numEnrolled < enrolled.length-1) {
	    enrolled[numEnrolled] = s;
	    numEnrolled = numEnrolled + 1;
	    s.taking[s.numTaking] = this;
	    s.numTaking = s.numTaking + 1;
	} else if (numWaiting < waiting.length-1) {
	    waiting[numWaiting] = s;
	    numWaiting = numWaiting + 1;
	}
    }

    void finishCourse() {
	int i = 0;
	while (i<numEnrolled) {
	    Student s = enrolled[i];
	    s.transcript[s.numTaken] = new TranscriptEntry(this, 'A');
	    s.numTaken = s.numTaken + 1;
	    i = i + 1;
	} 
	numEnrolled = 0;
	numWaiting = 0;
    }
}

class TranscriptEntry {
    Course course;
    char grade; 

    TranscriptEntry(Course c, char g) { course = c; grade = g; }
}
